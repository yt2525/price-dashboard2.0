#!/usr/bin/env python3
"""
scrape.py — fetch competitor prices for the Price Reconciliation Dashboard.

Reads  urls.json   (category -> product -> competitor -> {url, note})
Writes prices.json  (category -> product -> competitor -> price)

WHY PLAYWRIGHT: almost every marketplace here (G2G, G2A, Kinguin, Eneba,
Codashop, SEAGM, MooGold, itemku ...) renders prices with JavaScript and/or
sits behind bot protection, so plain HTTP requests return empty shells. We
drive a real headless Chromium instead.

PER-SITE ADAPTERS: each marketplace lays its price out differently, so every
domain gets its own small adapter function that knows where to read the price.
`generic_extract` is the last-resort fallback. The two concrete adapters below
(MooGold, SEAGM) are STARTING POINTS — selectors WILL need to be verified
against the live pages. Treat them as a template for the rest.

LOCAL RUN:
    pip install playwright
    python -m playwright install chromium
    python scrape.py                                   # all categories
    python scrape.py --categories "Spotify" --headful  # watch one category
    python scrape.py --categories "Spotify" --limit 15 --debug   # diagnose

--debug writes a ./debug/ folder with a screenshot per URL and a findings.json
listing, for each page, its title, whether it looks blocked, and every
price-looking number found. Use it to write/verify adapter selectors. Share
debug/findings.json + a couple of screenshots and exact selectors can be added.

Anti-bot reality: expect ~5-7 of the 10 sites to work reliably. Some need
stealth tweaks, slower pacing, or proxies; a few may resist entirely. Be
respectful: low concurrency, modest cadence (the workflow runs every 6h).
"""

import argparse
import asyncio
import json
import re
import sys
import time
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urlparse

from playwright.async_api import async_playwright

ROOT = Path(__file__).resolve().parent
URLS_FILE = ROOT / "urls.json"
OUT_FILE = ROOT / "prices.json"
REPORT_FILE = ROOT / "scrape_report.json"
DEBUG_DIR = ROOT / "debug"

# --- tuning knobs -----------------------------------------------------------
CONCURRENCY = 4            # parallel pages; keep low to stay polite / unblocked
NAV_TIMEOUT_MS = 25_000    # per-page navigation timeout
RETRIES = 1                # extra attempts on failure
PER_REQUEST_DELAY = 0.4    # seconds of jitter between starts (politeness)
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)
BLOCK_HINTS = ("just a moment", "captcha", "access denied", "cloudflare",
               "are you a human", "verify you are", "unusual traffic",
               "请稍候", "enable javascript")

debug_records = []  # populated when --debug

# --- price text parsing -----------------------------------------------------
# Matches "$12.34", "US$ 12.34", "12.34 USD", "RM 50", "€10,00", "S$ 9.90" etc.
_PRICE_RE = re.compile(
    r"(?:US\$|USD|RM|S\$|SGD|EUR|€|£|\$)\s*([0-9]{1,3}(?:[.,][0-9]{3})*(?:[.,][0-9]{1,2})?)"
    r"|([0-9]{1,3}(?:[.,][0-9]{3})*(?:[.,][0-9]{1,2})?)\s*(?:USD|EUR|SGD|MYR|RM)",
    re.IGNORECASE,
)


def _to_float(raw: str):
    """Normalise a price token to float, handling 1,234.56 and 1.234,56."""
    s = raw.strip()
    if "," in s and "." in s:
        if s.rfind(",") > s.rfind("."):
            s = s.replace(".", "").replace(",", ".")
        else:
            s = s.replace(",", "")
    elif "," in s:
        if re.search(r",\d{2}$", s):
            s = s.replace(",", ".")
        else:
            s = s.replace(",", "")
    try:
        v = float(s)
        return v if 0 < v < 100_000 else None
    except ValueError:
        return None


def prices_in_text(text: str):
    out = []
    for m in _PRICE_RE.finditer(text or ""):
        tok = m.group(1) or m.group(2)
        v = _to_float(tok)
        if v is not None:
            out.append(v)
    return out


_CUR = {"USD": "USD", "US$": "USD", "$": "USD", "EUR": "EUR", "€": "EUR",
        "GBP": "GBP", "£": "GBP", "JPY": "JPY", "CNY": "CNY", "CAD": "CAD",
        "MYR": "MYR", "RM": "MYR", "SGD": "SGD", "S$": "SGD", "QAR": "QAR",
        "AUD": "AUD", "USDT": "USDT", "USDC": "USDC"}


def parse_denomination(name):
    """Extract {amount, currency, region} from a product name.
    e.g. 'Spotify Gift Card USD 60' -> {amount:60.0, currency:'USD', region:None}
         'Steam Wallet Code RM50 (MY)' -> {amount:50.0, currency:'MYR', region:'MY'}
    """
    region = None
    m = re.search(r"\(([A-Z]{2,4})\)", name)
    if m:
        region = m.group(1)
    cur = amount = None
    m = re.search(r"(USD|EUR|GBP|JPY|CNY|CAD|MYR|RM|SGD|QAR|AUD|USDT|USDC|US\$|S\$|\$|€|£)\s?([0-9][0-9,\.]*)",
                  name, re.I)
    if m:
        cur = _CUR.get(m.group(1).upper().replace(" ", "")); amount = m.group(2)
    else:
        m = re.search(r"([0-9][0-9,\.]*)\s?(USD|EUR|GBP|JPY|CNY|CAD|MYR|RM|SGD|QAR|AUD)\b", name, re.I)
        if m:
            cur = _CUR.get(m.group(2).upper()); amount = m.group(1)
    if amount:
        try:
            amount = float(amount.replace(",", "").rstrip("."))
        except ValueError:
            amount = None
    return {"amount": amount, "currency": cur, "region": region}


def denom_in_text(text, denom):
    """True if the page/card text plausibly refers to this denomination's amount."""
    amt = denom.get("amount")
    if amt is None:
        return True  # nothing to match on -> don't exclude
    t = (text or "").replace(",", "")
    a_int = str(int(amt)) if amt == int(amt) else None
    a_dec = ("%g" % amt)
    pats = [p for p in {a_int, a_dec} if p]
    return any(re.search(r"(?<!\d)" + re.escape(p) + r"(?!\d)", t) for p in pats)


# --- currency + FX --------------------------------------------------------
FX = {"USD": 1.0}  # rates[X] = units of X per 1 USD


def load_fx():
    """Fetch USD-based FX rates once per run (free, no key). Falls back to static."""
    global FX
    try:
        with urllib.request.urlopen("https://open.er-api.com/v6/latest/USD", timeout=15) as r:
            data = json.loads(r.read().decode())
        rates = data.get("rates") or {}
        if rates:
            FX = rates
        FX["USD"] = 1.0
        print(f"FX loaded ({len(FX)} currencies).", flush=True)
    except Exception:
        FX = {"USD": 1.0, "MYR": 4.7, "EUR": 0.92, "SGD": 1.34, "GBP": 0.79,
              "JPY": 155.0, "CNY": 7.2, "CAD": 1.37, "AUD": 1.5}
        print("FX fetch failed — using fallback rates.", flush=True)


def to_usd(value, cur):
    if value is None:
        return None
    rate = FX.get((cur or "USD").upper())
    if not rate:
        return round(value, 2)  # unknown currency -> assume already USD
    return round(value / rate, 2)


def parse_price_currency(text):
    """From a price string, return (amount_float, currency_code) or None."""
    s = (text or "").strip()
    if not s:
        return None
    if re.search(r"\bRM|\bMYR", s, re.I):       # RM470 or RM 470 or MYR
        cur = "MYR"
    elif re.search(r"S\$|\bSGD", s, re.I):
        cur = "SGD"
    elif re.search(r"€|\bEUR", s, re.I):
        cur = "EUR"
    elif re.search(r"£|\bGBP", s, re.I):
        cur = "GBP"
    elif re.search(r"\bJPY|¥", s, re.I):
        cur = "JPY"
    else:
        cur = "USD"
    vals = prices_in_text(s)
    if not vals:
        return None
    return (min(vals), cur)


# JS: find the price for a SPECIFIC denomination on an all-on-one-page listing.
# Strategy: locate the smallest element whose text is the denomination *label*
# (e.g. "100 USD"), then climb to the nearest ancestor that holds a price
# element (sel) and read it. This avoids matching the whole grid (which would
# return the first/cheapest price for every denomination).
_MATCH_JS = r"""
(args) => {
  const {sel, amt} = args;
  const priceRe = /(US\$|USD|RM|MYR|S\$|SGD|€|£|\$)\s?\d[\d.,]*|\d[\d.,]*\s?(USD|EUR|MYR|SGD|RM)/i;
  if (amt == null) {
    for (const pe of document.querySelectorAll(sel)) {
      if (priceRe.test(pe.textContent || '')) return pe.textContent.trim();
    }
    return null;
  }
  // denomination label phrase: "100 USD" | "USD 100" | "USD100" | "US$100"
  const labelRe = new RegExp('(?:(?<!\\d)' + amt + '\\s*USD|USD\\s*' + amt + '(?!\\d)|US\\$\\s*' + amt + '(?!\\d))', 'i');
  let label = null, len = 1e9;
  for (const el of document.querySelectorAll('div,span,li,a,p,button,label,td,h1,h2,h3')) {
    const t = (el.textContent || '').replace(/,/g, '');
    if (t.length > 150) continue;          // skip big containers
    if (labelRe.test(t) && t.length < len) { label = el; len = t.length; }
  }
  if (!label) return null;
  // climb from the label to the nearest ancestor that contains a price (sel)
  let node = label;
  for (let i = 0; i < 7 && node; i++) {
    if (node.querySelectorAll) {
      for (const pe of node.querySelectorAll(sel)) {
        if (priceRe.test(pe.textContent || '')) return pe.textContent.trim();
      }
    }
    node = node.parentElement;
  }
  return null;
}
"""


async def _matched_price(page, sel, denom):
    amt = denom.get("amount")
    amt_s = str(int(amt)) if (amt is not None and amt == int(amt)) else (str(amt) if amt is not None else None)
    try:
        txt = await page.evaluate(_MATCH_JS, {"sel": sel, "amt": amt_s})
    except Exception:
        txt = None
    return parse_price_currency(txt) if txt else None


async def generic_extract(page, url, denom):
    """Last-resort: scan visible text and return the lowest plausible price + currency."""
    try:
        body = await page.inner_text("body")
    except Exception:
        return None
    return parse_price_currency(body)


# --- site-specific adapters (return (value, currency); selectors from findings) ---
async def adapter_codashop(page, url, denom):
    # Listing page: each denomination card has the amount label + a price in
    # span.price-section__price__price-container__amount (e.g. "$100.00"). USD.
    return await _matched_price(page, "[class*='price-container__amount']", denom)


async def adapter_seagm(page, url, denom):
    # Listing page: each card shows the amount + a <b> price (b.price_origional
    # is the crossed-out original, so exclude it). Usually MYR -> converted.
    return await _matched_price(page, "b:not(.price_origional)", denom)


async def adapter_eneba(page, url, denom):
    # Direct product page: the live price sits in the buy button (the other
    # RM value is a crossed-out original). Usually MYR -> converted.
    try:
        txt = await page.evaluate(r"""
        () => {
          const re = /(RM|MYR|US\$|USD|€|£|S\$|SGD|\$)\s?\d[\d.,]*/i;
          for (const b of document.querySelectorAll('button')) {
            const m = (b.textContent || '').match(re);
            if (m) return m[0];
          }
          const el = document.querySelector("[class*='price'],[data-testid*='price']");
          return el ? el.textContent.trim() : null;
        }
        """)
    except Exception:
        txt = None
    return parse_price_currency(txt) if txt else None


async def adapter_moogold(page, url, denom):
    # WooCommerce variable product: select the matching variation, then read price.
    amt = denom.get("amount")
    if amt is not None:
        label = str(int(amt)) if amt == int(amt) else str(amt)
        try:
            for b in await page.query_selector_all(
                    ".variable-item-span, .variable-item, [class*=variable-item]"):
                t = await b.inner_text()
                if t and re.search(r"(?<!\d)" + re.escape(label) + r"(?!\d)", t) and "USD" in t:
                    await b.click()
                    await page.wait_for_timeout(1200)
                    break
        except Exception:
            pass
    for sel in [".single_variation .woocommerce-Price-amount bdi",
                ".woocommerce-Price-amount bdi", ".woocommerce-Price-amount"]:
        try:
            el = await page.query_selector(sel)
            if el:
                pc = parse_price_currency(await el.inner_text())
                if pc:
                    return pc
        except Exception:
            pass
    return await generic_extract(page, url, denom)


async def adapter_kinguin(page, url, denom):
    # Recorded via codegen: the live price sits in the main offer section.
    # data-test attribute is stable. (Currency = USD on a US proxy.)
    for sel in ['[data-test="main-offer__price-section"]',
                '[data-test*="price-section"]', '[data-test*="price"]']:
        try:
            el = await page.query_selector(sel)
            if el:
                pc = parse_price_currency(await el.inner_text())
                if pc:
                    return pc
        except Exception:
            pass
    return await generic_extract(page, url, denom)


async def adapter_joytify(page, url, denom):
    # LapakGaming/Joytify: brand landing page lists denominations as cards like
    # "PlayStation USA 100 USD  From $93.08". Find the card matching the
    # denomination and read its $ price (already USD).
    amt = denom.get("amount")
    if amt is None:
        return await generic_extract(page, url, denom)
    amt_s = str(int(amt)) if amt == int(amt) else str(amt)
    try:
        raw = await page.evaluate(r"""
        (amt) => {
          const re = new RegExp('(?<!\\d)' + amt + '\\s*USD', 'i');
          let best = null, bestLen = 1e9;
          for (const el of document.querySelectorAll('a,div,li,button,span')) {
            const t = (el.textContent || '').replace(/\s+/g, ' ');
            if (!re.test(t.replace(/,/g, ''))) continue;
            const m = t.match(/\$\s?([\d.,]+)/);
            if (m && t.length < bestLen) { best = '$' + m[1]; bestLen = t.length; }
          }
          return best;
        }
        """, amt_s)
    except Exception:
        raw = None
    return parse_price_currency(raw) if raw else await generic_extract(page, url, denom)


async def adapter_itemku(page, url, denom):
    # itemku: selected listing's price shows in #catalog-form-order
    # (e.g. "USD 93.38"). Region North America -> USD; else MYR -> converted.
    for sel in ['#catalog-form-order', '[id*=catalog-form-order]', '[id*=catalog-form]']:
        try:
            el = await page.query_selector(sel)
            if el:
                pc = parse_price_currency(await el.inner_text())
                if pc:
                    return pc
        except Exception:
            pass
    return await generic_extract(page, url, denom)


async def adapter_unipin(page, url, denom):
    # UniPin (region = United States -> USD): click the denomination button,
    # then read the standalone "USD 99.36" price shown below it. Best-effort.
    amt = denom.get("amount")
    if amt is not None:
        label = str(int(amt)) if amt == int(amt) else str(amt)
        try:
            for b in await page.query_selector_all("button, a, [class*=denom], [class*=product]"):
                t = await b.inner_text()
                if t and re.search(r"(?<!\d)" + re.escape(label) + r"(?!\d)", t) and "USD" in t:
                    await b.click()
                    await page.wait_for_timeout(1200)
                    break
        except Exception:
            pass
    try:
        raw = await page.evaluate(r"""
        () => {
          for (const el of document.querySelectorAll('span,div,p,b,strong')) {
            const t = (el.textContent || '').trim().replace(/\s+/g, ' ');
            if (/^(USD|US\$|\$)\s?\d[\d.,]+$/i.test(t)) return t;
          }
          return null;
        }
        """)
    except Exception:
        raw = None
    return parse_price_currency(raw) if raw else await generic_extract(page, url, denom)


# domain -> adapter. Unlisted domains use generic_extract.
ADAPTERS = {
    "codashop.com": adapter_codashop,
    "seagm.com": adapter_seagm,
    "eneba.com": adapter_eneba,
    "moogold.com": adapter_moogold,
    "kinguin.net": adapter_kinguin,
    "joytify.com": adapter_joytify,   # LapakGaming
    "itemku.com": adapter_itemku,
    "unipin.com": adapter_unipin,
    # Still need work: g2g.com (search flow), g2a.com, offgamers.com (search flow)
}


def adapter_for(url):
    host = urlparse(url).netloc.replace("www.", "").lower()
    for dom, fn in ADAPTERS.items():
        if host.endswith(dom):
            return fn
    return generic_extract


def _safe(s, n=60):
    return re.sub(r"[^A-Za-z0-9._-]+", "_", str(s))[:n]


async def collect_debug(page, task):
    """Save a screenshot + record what the page actually contains."""
    rec = {"comp": task["comp"], "url": task["url"], "category": task["sheet"],
           "product": task["pname"], "title": None, "blocked": False,
           "candidates": [], "adapter": adapter_for(task["url"]).__name__}
    try:
        rec["title"] = await page.title()
    except Exception:
        pass
    try:
        body = await page.inner_text("body")
        low = (body or "").lower()
        rec["blocked"] = any(h in low for h in BLOCK_HINTS)
        rec["candidates"] = sorted(set(prices_in_text(body)))[:15]
    except Exception:
        pass
    # Capture leaf elements that look like prices, with a CSS selector for each,
    # so adapters can target the exact price location.
    try:
        rec["priceEls"] = await page.evaluate(r"""
        () => {
          const re = /(US\$|USD|RM|MYR|S\$|SGD|€|£|\$)\s?\d[\d.,]*|\d[\d.,]*\s?(USD|EUR|MYR|SGD|RM)/i;
          const out = [];
          for (const el of document.querySelectorAll('body *')) {
            if (el.children.length) continue;           // leaf nodes only
            const t = (el.textContent || '').trim();
            if (!t || t.length > 40 || !re.test(t)) continue;
            let sel = el.tagName.toLowerCase();
            if (el.id) sel += '#' + el.id;
            if (typeof el.className === 'string' && el.className.trim())
              sel += '.' + el.className.trim().split(/\s+/).slice(0, 3).join('.');
            let par = el.parentElement;
            let pcls = par && typeof par.className === 'string' ? par.className.trim().split(/\s+/).slice(0,2).join('.') : '';
            out.push({ text: t, sel, parent: (par ? par.tagName.toLowerCase() : '') + (pcls ? '.' + pcls : '') });
            if (out.length >= 30) break;
          }
          return out;
        }
        """)
    except Exception:
        rec["priceEls"] = []
    shot = DEBUG_DIR / f"{_safe(task['sheet'])}__{_safe(task['pname'],40)}__{_safe(task['comp'])}.png"
    try:
        await page.screenshot(path=str(shot), full_page=False)
        rec["screenshot"] = shot.name
    except Exception:
        pass
    debug_records.append(rec)


# Hook for per-site URL tweaks. NOTE: do not rewrite Eneba's locale — its slugs
# differ per region, so /en-us/ 404s. We keep the given URL and convert currency.
def usd_url(url):
    return url


# --- fetching ---------------------------------------------------------------
async def fetch_one(context, task, results, report):
    url, comp = task["url"], task["comp"]
    fn = adapter_for(url)
    for attempt in range(RETRIES + 1):
        page = await context.new_page()
        try:
            await page.route(
                "**/*",
                lambda r: r.abort()
                if r.request.resource_type in ("image", "media", "font")
                else r.continue_(),
            )
            await page.goto(usd_url(url), timeout=NAV_TIMEOUT_MS, wait_until="domcontentloaded")
            # Give JS-heavy / lazy-loading marketplaces time to render prices.
            try:
                await page.wait_for_load_state("networkidle", timeout=8000)
            except Exception:
                pass
            try:
                await page.mouse.wheel(0, 2400)   # trigger lazy-loaded offers/prices
            except Exception:
                pass
            await page.wait_for_timeout(3000)
            if ARGS.debug:
                await collect_debug(page, task)
            denom = parse_denomination(task["pname"])
            result = await fn(page, url, denom)   # (value, currency) or None
            await page.close()
            if result is not None:
                value, cur = result
                usd = to_usd(value, cur)
                if usd is not None and usd > 0:
                    results.setdefault(task["sheet"], {}).setdefault(task["pname"], {})[comp] = usd
                    report["ok"] += 1
                    return
        except Exception as e:
            report["errors"].append(f'{comp} {url[:60]} :: {type(e).__name__}')
            try:
                await page.close()
            except Exception:
                pass
        await asyncio.sleep(0.8 * (attempt + 1))
    report["failed"] += 1


async def run(tasks):
    results, report = {}, {"ok": 0, "failed": 0, "errors": []}
    load_fx()  # USD conversion rates for this run
    sem = asyncio.Semaphore(1 if ARGS.debug else CONCURRENCY)

    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=not ARGS.headful)
        context = await browser.new_context(user_agent=USER_AGENT, locale="en-US")

        async def worker(t):
            async with sem:
                await asyncio.sleep(PER_REQUEST_DELAY)
                await fetch_one(context, t, results, report)

        done = 0
        for fut in asyncio.as_completed([worker(t) for t in tasks]):
            await fut
            done += 1
            if done % 25 == 0 or done == len(tasks):
                print(f"  {done}/{len(tasks)} fetched "
                      f"(ok={report['ok']} fail={report['failed']})", flush=True)
        await browser.close()
    return results, report


# Competitors without a reliable adapter yet — held off so they don't add junk.
# (MooGold's variable-product price doesn't render via standard selectors.)
SKIP_COMPS = {"OG", "G2A", "G2G", "Moogold"}


def build_tasks(data, only_categories, limit):
    tasks = []
    for cat, block in data["categories"].items():
        if only_categories and cat not in only_categories:
            continue
        for product in block["products"]:
            for comp, info in product["urls"].items():
                if comp in SKIP_COMPS:
                    continue
                tasks.append({"sheet": cat, "pname": product["name"],
                              "comp": comp, "url": info["url"], "note": info.get("note")})
    return tasks[:limit] if limit else tasks


def main():
    if not URLS_FILE.exists():
        sys.exit(f"Missing {URLS_FILE} — generate it from the products spreadsheet first.")
    data = json.loads(URLS_FILE.read_text(encoding="utf-8"))

    only = set(c.strip() for c in ARGS.categories.split(",")) if ARGS.categories else None
    tasks = build_tasks(data, only, ARGS.limit)
    if ARGS.debug:
        DEBUG_DIR.mkdir(exist_ok=True)
    print(f"Scraping {len(tasks)} URLs across "
          f"{len(only) if only else len(data['categories'])} categories"
          f"{' [DEBUG]' if ARGS.debug else ''}…", flush=True)

    t0 = time.time()
    results, report = asyncio.run(run(tasks))

    payload = {"generated": datetime.now(timezone.utc).isoformat(),
               "source": "scrape.py", "prices": results}
    OUT_FILE.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")

    report["elapsed_sec"] = round(time.time() - t0, 1)
    report["errors"] = report["errors"][:50]
    REPORT_FILE.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")

    if ARGS.debug:
        (DEBUG_DIR / "findings.json").write_text(
            json.dumps(debug_records, ensure_ascii=False, indent=2), encoding="utf-8")
        print("\n--- DEBUG SUMMARY (per URL) ---")
        for r in debug_records:
            flag = "BLOCKED" if r["blocked"] else ("HIT" if r["candidates"] else "empty")
            print(f"  [{flag:7}] {r['comp']:12} cands={r['candidates'][:5]}  {r['url'][:55]}")
        print(f"\nScreenshots + findings.json in: {DEBUG_DIR}")

    print(f"\nDone in {report['elapsed_sec']}s — ok={report['ok']} "
          f"failed={report['failed']}. Wrote {OUT_FILE.name}.", flush=True)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--categories", default="", help="comma-separated subset, e.g. 'Steam,Spotify'")
    ap.add_argument("--limit", type=int, default=0, help="cap total fetches (smoke test)")
    ap.add_argument("--headful", action="store_true", help="show the browser window")
    ap.add_argument("--debug", action="store_true", help="save screenshots + findings.json per URL")
    ARGS = ap.parse_args()
    main()
