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

# Sentinel: the product page loaded but the item is sold out / unavailable, so we
# record "N/A" instead of a (possibly stale or wrong) price. The dashboard renders
# this as N/A and auto-replaces it with a price on the next run if stock returns.
NA = "N/A"
_SOLDOUT_RE = re.compile(
    r"sold\s*out|out[\s-]*of[\s-]*stock|currently unavailable|temporarily unavailable|"
    r"no longer available|not available|notify me when|coming soon|无货|售罄|缺货",
    re.I)


def looks_sold_out(text):
    return bool(text and _SOLDOUT_RE.search(text))


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
    return {"amount": amount, "currency": cur, "region": region,
            "nums": denom_numbers(name), "words": denom_words(name)}


# Generic filler / unit words that don't help identify a specific product card.
_DENOM_STOP = {
    "gift", "card", "cards", "code", "codes", "voucher", "vouchers", "key", "keys",
    "global", "region", "the", "top", "up", "value", "points", "point", "pts",
    "usd", "eur", "gbp", "jpy", "cny", "cad", "myr", "rm", "sgd", "qar", "aud",
    "usdt", "usdc", "yen", "for", "us", "me",
}


def denom_words(name):
    """Distinguishing lowercase words from a product name (brand + variant), used
    to match/disambiguate cards when numbers are absent or shared. e.g.
        'Lunite Subscription'        -> ['lunite', 'subscription']
        'GASH 5000 Points (HK)'      -> ['gash']
        'GoCash US$ 15'              -> ['gocash']
    """
    s = re.sub(r"\([^)]*\)", " ", name).lower()
    out = []
    for tok in re.findall(r"[a-z]+", s):
        if len(tok) >= 2 and tok not in _DENOM_STOP and tok not in out:
            out.append(tok)
    return out


def denom_numbers(name):
    """Numbers to match a denomination by, handling format differences.
    Catalog writes "base + bonus" (e.g. 1,980 + 260 Crystals) but sites label by
    the TOTAL (2240). So return every number in the name PLUS their sum:
        "Genshin Impact 1,980 + 260 Crystals" -> [1980, 260, 2240]
        "PlayStation USD100 Gift Cards (US)"  -> [100]
    """
    s = re.sub(r"\([A-Za-z]{2,4}\)", " ", name)          # drop region codes like (US)
    nums = []
    for x in re.findall(r"\d[\d,]*", s):
        try:
            n = int(x.replace(",", ""))
        except ValueError:
            continue
        if n > 0 and n not in nums:
            nums.append(n)
    if len(nums) >= 2:                                    # add the base+bonus total
        nums.append(sum(nums))
    return nums


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
    import ssl
    url = "https://open.er-api.com/v6/latest/USD"
    # Try normally first, then with an unverified SSL context. macOS's bundled
    # Python often lacks CA certs, so the verified call raises and we'd otherwise
    # drop to stale fallbacks even though the network is fine.
    for ctx in (None, ssl._create_unverified_context()):
        try:
            with urllib.request.urlopen(url, timeout=15, context=ctx) as r:
                data = json.loads(r.read().decode())
            rates = data.get("rates") or {}
            if rates:
                FX = rates
                FX["USD"] = 1.0
                print(f"FX loaded ({len(FX)} currencies).", flush=True)
                return
        except Exception:
            continue
    # Offline fallback — kept current (USD per 1 unit shown as units per USD).
    FX = {"USD": 1.0, "MYR": 4.06, "EUR": 0.87, "SGD": 1.28, "GBP": 0.74,
          "JPY": 155.0, "CNY": 7.2, "CAD": 1.37, "AUD": 1.5}
    print("FX fetch failed — using fallback rates (MYR 4.06).", flush=True)


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
  const {sel, nums, words} = args;   // nums e.g. [1980,260,2240]; words e.g. ['lunite','subscription']
  const priceRe = /(US\$|USD|RM|MYR|S\$|SGD|€|£|\$)\s?\d[\d.,]*|\d[\d.,]*\s?(USD|EUR|MYR|SGD|RM)/i;
  const ws = (words || []).map(w => String(w).toLowerCase());
  if ((!nums || !nums.length) && !ws.length) {
    for (const pe of document.querySelectorAll(sel)) {
      if (priceRe.test(pe.textContent || '')) return pe.textContent.trim();
    }
    return null;
  }
  const numRes = (nums || []).map(n => new RegExp('(?<![\\d.])' + n + '(?![\\d.])'));
  const GATE = /USD|EUR|GBP|JPY|CNY|CAD|MYR|RM|SGD|QAR|AUD|USDT|USDC|Diamond|Crystal|Genesis|Point|Coin|Gold|Credit|Shard|Lunite|Gem|Rbx|Roblox|Robux|Oneiric|Monochrome|Bonus|Welkin|Pass|Nitro|Premium|Wallet|Day|Days|Month|Months|Year|Years|Gift|Card|Voucher|Subscription|GASH|GoCash|Cash|NCoin|NCSOFT|Flexepin|Binance|Crypto|Steam|Apple|iTunes|Honkai|Pin|Yen/i;
  // Find the denomination LABEL: the small element scoring highest on target
  // numbers (weighted heavily) plus target name-words (the tie-breaker / the
  // only signal when a product has no number, e.g. "Lunite Subscription").
  let label = null, bestScore = 0, bestLen = 1e9;
  for (const el of document.querySelectorAll('div,span,li,a,p,button,label,td,h1,h2,h3,h4')) {
    const t = (el.textContent || '').replace(/,/g, '');
    if (t.length > 90) continue;
    const tl = t.toLowerCase();
    let numScore = 0; for (const re of numRes) if (re.test(t)) numScore++;
    let wordScore = 0; for (const w of ws) if (tl.includes(w)) wordScore++;
    const score = numScore * 10 + wordScore;
    if (score === 0) continue;
    // accept titles via the keyword gate, OR any element that hit a name-word
    if (!GATE.test(t) && wordScore === 0) continue;
    if (score > bestScore || (score === bestScore && t.length < bestLen)) {
      label = el; bestScore = score; bestLen = t.length;
    }
  }
  if (!label) return null;
  // climb from the matched label to the nearest ancestor holding a price (sel)
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
    try:
        txt = await page.evaluate(_MATCH_JS, {"sel": sel, "nums": denom.get("nums") or [],
                                              "words": denom.get("words") or []})
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
    # is the crossed-out original, so exclude it). We load SEAGM via /en-us/
    # (see usd_url), which prices natively in USD — so use that USD figure
    # DIRECTLY with no FX conversion. If the matched price isn't USD, the en-us
    # locale didn't apply (we'd otherwise convert a cheaper regional price and
    # report the wrong number), so record N/A instead.
    pc = await _matched_price(page, "b:not(.price_origional)", denom)
    if pc:
        value, cur = pc
        if cur == "USD":
            return (value, "USD")          # use USD as-is, no converter
        return NA                          # non-USD => en-us didn't take; don't convert
    return None


_ENEBA_JS = r"""
(args) => {
  const {nums, cur} = args;
  // Eneba product pages list EVERY denomination as a grid card titled by its
  // face value (e.g. "20 USD", "200 QAR", "500 CAD") with the buyer price shown
  // in $ underneath (e.g. "$19.65") plus a "1.02 USD per $1" ratio. Match the
  // card by face value (number [+ face currency]) then read the $ buyer price.
  const numRes = (nums || []).map(n => new RegExp('(?<![\\d.])' + n + '(?![\\d.])'));
  const curRe = cur ? new RegExp('\\b' + cur + '\\b', 'i') : null;
  // Collect EVERY short element whose face value matches (the grid card title AND
  // the "Value:" header both say e.g. "150 CAD"). We try them all below, because
  // only the grid card has the price next to it.
  const labels = [];
  for (const el of document.querySelectorAll('div,span,li,a,p,button,label,h1,h2,h3,h4')) {
    const t = (el.textContent || '').replace(/,/g, '');
    if (t.length > 40) continue;                 // card titles are short
    let s = 0; for (const re of numRes) if (re.test(t)) s++;
    if (numRes.length && s === 0) continue;
    if (curRe && curRe.test(t)) s += 1;          // currency match is a bonus, not required
    labels.push({ el, score: s, len: t.length });
  }
  if (!labels.length) return null;
  labels.sort((a, b) => b.score - a.score || a.len - b.len);   // best candidates first
  // For each candidate, climb to its OWN card (a small container) and read the $
  // buyer price. The "Value:" header has no price nearby, so it's skipped and the
  // real grid card wins. PRICE WINS even if the product is sold out. Only when no
  // candidate has a price in its card do we report sold-out -> N/A.
  // The price regex stops after 2 decimals so "$118.12" next to the "1.27 per $1"
  // ratio isn't misread as 118.121.
  const soldRe = /sold\s*out|out of stock|currently unavailable|temporarily unavailable|notify me|sorry/i;
  const priceRe = /\$\s?(\d[\d,]*(?:\.\d{1,2})?)/g;
  let sold = false;
  for (const { el } of labels) {
    let node = el;
    for (let i = 0; i < 5 && node; i++) {
      const txt = node.textContent || '';
      if (txt.length < 160) {
        const vals = [...txt.matchAll(priceRe)]
          .map(m => parseFloat(m[1].replace(/,/g, ''))).filter(v => !isNaN(v) && v > 0);
        if (vals.length) return { price: Math.max(...vals) };
      }
      if (soldRe.test(txt) && txt.length < 200) sold = true;
      node = node.parentElement;
    }
  }
  return sold ? { soldout: true } : null;
}
"""


async def adapter_eneba(page, url, denom):
    # Grid-match the denomination card and read its $ (USD) buyer price. If that
    # specific card is sold out, record N/A. NOTE: we deliberately never fall
    # back to a generic text scan here — on Eneba that grabs a face value like
    # "100 USD" (=100) and reports it as a price.
    try:
        res = await page.evaluate(_ENEBA_JS, {"nums": denom.get("nums") or [],
                                              "cur": denom.get("currency")})
    except Exception:
        res = None
    if getattr(ARGS, "debug", False):
        print(f"    [ENEBA-DEBUG] {url[:75]} nums={denom.get('nums')} "
              f"cur={denom.get('currency')} grid_res={res}", flush=True)
    if isinstance(res, dict):
        if isinstance(res.get("price"), (int, float)) and res["price"] > 0:
            return (round(float(res["price"]), 2), "USD")
        if res.get("soldout"):
            return NA
    # Single-offer pages (no value grid, e.g. Nutaku) show a "FEATURED OFFER"
    # plus a seller list. The featured offer isn't always the cheapest, so scope
    # to the offers area (a few ancestors up from the "featured offer" label) and
    # take the LOWEST $ seller price there. Scoping avoids grabbing prices from
    # unrelated "you might also like" items lower on the page.
    try:
        txt = await page.evaluate(r"""
        () => {
          let fo = null;
          for (const el of document.querySelectorAll('div,section,span,p,strong,b')) {
            const t = el.textContent || '';
            if (t.length < 300 && /featured offer/i.test(t)) { fo = el; break; }
          }
          let scope = document.body;
          if (fo) { let n = fo; for (let i = 0; i < 5 && n.parentElement; i++) n = n.parentElement; scope = n; }
          const txt = (scope && scope.innerText) || '';
          const vals = [...txt.matchAll(/\$\s?(\d[\d.,]*\.\d{2})\b/g)]
            .map(m => parseFloat(m[1].replace(/,/g, ''))).filter(v => !isNaN(v) && v > 0);
          return vals.length ? 'USD ' + Math.min(...vals) : null;
        }
        """)
    except Exception:
        txt = None
    if txt:
        pc = parse_price_currency(txt)
        if pc:
            return pc
    # The requested denomination has no price on the page (its card is sold out or
    # not listed). Do NOT fall back to a buy-button / generic scan — on Eneba those
    # grab a stray price from an AVAILABLE card (e.g. the cheap "1 USD" = $1.25) and
    # report it for a sold-out denomination. Record N/A instead.
    return NA


async def adapter_moogold(page, url, denom):
    # WooCommerce variable product. All variations (with display_price) are
    # embedded in form[data-product_variations] JSON, so we don't need to click
    # swatches. Match the variation by denomination numbers and read its price.
    nums = denom.get("nums") or []
    raw = None
    try:
        raw = await page.evaluate(
            r"""(nums) => {
              const form = document.querySelector('form.variations_form, [data-product_variations]');
              if (!form) return null;
              let arr;
              try { arr = JSON.parse(form.getAttribute('data-product_variations')); }
              catch (e) { return null; }
              if (!Array.isArray(arr) || !arr.length) return null;
              const numRes = (nums || []).map(n => new RegExp('(?<![\\d.])' + n + '(?![\\d.])'));
              let best = null, bestScore = -1;
              for (const v of arr) {
                const at = Object.values(v.attributes || {}).join(' ').replace(/,/g, '');
                let sc = 0; for (const re of numRes) if (re.test(at)) sc++;
                if (sc > bestScore) { bestScore = sc; best = v; }
              }
              // if no number matched at all and there are several variations, bail
              if (!best || (bestScore <= 0 && arr.length > 1)) return null;
              if (best.display_price == null) return null;
              const symEl = document.querySelector('.woocommerce-Price-currencySymbol');
              const s = symEl ? symEl.textContent : '';
              let cur = 'USD';
              if (/RM|MYR/i.test(s)) cur = 'MYR';
              else if (/€|EUR/i.test(s)) cur = 'EUR';
              else if (/£|GBP/i.test(s)) cur = 'GBP';
              else if (/S\$|SGD/i.test(s)) cur = 'SGD';
              return cur + ' ' + best.display_price;
            }""",
            nums,
        )
    except Exception:
        raw = None
    if raw:
        pc = parse_price_currency(raw)
        if pc:
            return pc
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
    # No price found: if the listing says it's sold out / unavailable, record N/A
    # rather than letting a stray number through the generic scan.
    try:
        body = await page.inner_text("body")
    except Exception:
        body = ""
    if looks_sold_out(body):
        return NA
    return await generic_extract(page, url, denom)


# JS: match a denomination card by its numbers (e.g. [3688] or [1980,260,2240])
# and return that card's text — used by sites that show "<denom> ... From $X"
# (Joytify/LapakGaming, etc.). The $ price is the only currency-marked number,
# so parse_price_currency() picks it out; the diamond/crystal counts are ignored.
_MATCH_CARD_JS = r"""
(args) => {
  const {nums, words} = args;
  const priceRe = /(US\$|USD|RM|MYR|S\$|SGD|€|£|\$)\s?\d[\d.,]*|\d[\d.,]*\s?(USD|EUR|MYR|SGD|RM)/i;
  const ws = (words || []).map(w => String(w).toLowerCase());
  if ((!nums || !nums.length) && !ws.length) return null;
  const numRes = (nums || []).map(n => new RegExp('(?<![\\d.])' + n + '(?![\\d.])'));
  const GATE = /USD|EUR|GBP|JPY|CNY|CAD|MYR|RM|SGD|QAR|AUD|USDT|USDC|Diamond|Crystal|Genesis|Point|Coin|Gold|Credit|Shard|Lunite|Gem|Rbx|Roblox|Robux|Oneiric|Monochrome|Bonus|Welkin|Pass|Nitro|Premium|Wallet|Day|Days|Month|Months|Year|Years|Gift|Card|Voucher|Subscription|GASH|GoCash|Cash|NCoin|NCSOFT|Flexepin|Binance|Crypto|Steam|Apple|iTunes|Honkai|Pin|Yen/i;
  let label = null, bestScore = 0, bestLen = 1e9;
  for (const el of document.querySelectorAll('div,span,li,a,p,button,label,td,h1,h2,h3,h4')) {
    const t = (el.textContent || '').replace(/,/g, '');
    if (t.length > 90) continue;
    const tl = t.toLowerCase();
    let numScore = 0; for (const re of numRes) if (re.test(t)) numScore++;
    let wordScore = 0; for (const w of ws) if (tl.includes(w)) wordScore++;
    const score = numScore * 10 + wordScore;
    if (score === 0) continue;
    if (!GATE.test(t) && wordScore === 0) continue;
    if (score > bestScore || (score === bestScore && t.length < bestLen)) {
      label = el; bestScore = score; bestLen = t.length;
    }
  }
  if (!label) return null;
  let node = label;
  for (let i = 0; i < 7 && node; i++) {
    if (priceRe.test(node.textContent || '')) return {text: node.textContent.trim(), hasPrice: true};
    node = node.parentElement;
  }
  // Matched the denomination card but found no price on it -> return its text
  // anyway so the caller can tell "out of stock" apart from "no match".
  return {text: label.textContent.trim(), hasPrice: false};
}
"""


async def _matched_card(page, denom):
    try:
        res = await page.evaluate(_MATCH_CARD_JS, {"nums": denom.get("nums") or [],
                                                   "words": denom.get("words") or []})
    except Exception:
        res = None
    return res  # {text, hasPrice} dict, or None if the denomination wasn't found


async def adapter_joytify(page, url, denom):
    # LapakGaming/Joytify: brand landing lists denominations as cards like
    # "3688 Diamonds 3099 + 589 Bonus From $49.43" or "PlayStation USA 100 USD From $93.08".
    # Match the card by its number(s)/total and read the $ price.
    #
    # Stock handling: if the matched card shows a price, record it. If the card
    # is matched but carries no price because it's out of stock (sold out / not
    # available), record N/A instead of falling through to a stray number. The
    # dashboard renders N/A and auto-replaces it with a real price on the next
    # run once the denomination is back in stock.
    res = await _matched_card(page, denom)
    if isinstance(res, dict):
        txt = res.get("text") or ""
        if res.get("hasPrice"):
            pc = parse_price_currency(txt)
            if pc:
                return pc
        if looks_sold_out(txt):
            return NA
    return await generic_extract(page, url, denom)


# itemku is an all-on-one-page listing (like SEAGM): the "Select Product" grid
# shows one card per denomination, each with a label ("USD $10") and its own
# orange price (.text-[#F46200], e.g. "USD 9.42"). The price is a SIBLING of the
# label, so we find each card (the ancestor holding exactly one price element),
# score its label text against the denomination numbers, and read the matching
# card's price. Using #catalog-form-order instead returns the selected/default
# (cheapest) product for every denomination — the bug this replaces.
_ITEMKU_JS = r"""
(nums) => {
  if (!nums || !nums.length) return null;
  const numRes = nums.map(n => new RegExp('(?<![\\d.])' + n + '(?![\\d.])'));
  const priceEls = [...document.querySelectorAll('[class*="F46200"]')];
  let best = null, bestScore = 0;
  for (const pe of priceEls) {
    let node = pe, card = null;
    for (let i = 0; i < 5 && node; i++) {
      const c = node.querySelectorAll ? node.querySelectorAll('[class*="F46200"]').length : 0;
      if (c === 1) card = node; else if (card) break;
      node = node.parentElement;
    }
    if (!card) continue;
    const priceTxt = pe.textContent || '';
    const cardTxt = (card.textContent || '').replace(priceTxt, ' ').replace(/,/g, '');
    let score = 0; for (const re of numRes) if (re.test(cardTxt)) score++;
    if (score > bestScore) { bestScore = score; best = priceTxt.trim(); }
  }
  return bestScore > 0 ? best : null;
}
"""


async def adapter_itemku(page, url, denom):
    nums = denom.get("nums") or []
    # itemku collapses the denomination grid ("Lihat N lainnya" / "Show N more"),
    # so higher denoms (e.g. 10000, 22500 Robux) aren't in the DOM until expanded.
    # Click any show-more toggle (repeatedly) before matching.
    for _ in range(3):
        try:
            clicked = await page.evaluate(r"""
            () => {
              const re = /lihat.*lainnya|show\s*\d*\s*more|lihat selengkapnya|show more|see more/i;
              for (const el of document.querySelectorAll('button,a,span,div')) {
                const t = (el.textContent || '').trim();
                if (t && t.length < 40 && re.test(t)) { el.click(); return true; }
              }
              return false;
            }
            """)
        except Exception:
            clicked = False
        if not clicked:
            break
        await page.wait_for_timeout(900)
    raw = None
    try:
        raw = await page.evaluate(_ITEMKU_JS, nums)
    except Exception:
        raw = None
    if raw:
        pc = parse_price_currency(raw)
        if pc:
            return pc
    # No matching denomination card found -> N/A rather than a wrong fallback
    # price (the generic scan would grab the cheapest card on the page).
    try:
        body = await page.inner_text("body")
    except Exception:
        body = ""
    return NA if looks_sold_out(body) else None


async def adapter_unipin(page, url, denom):
    # UniPin only has regional storefronts; our catalog uses the MY site, which
    # prices in MYR/RM. Per requirement we record that figure DIRECTLY as the USD
    # value (no FX conversion). Match the denomination card on the grid (by number
    # + name-words, e.g. "60 Oneiric Shard", "Express Supply Pass").
    pc = await _matched_price(page, "span,div,p,b,strong", denom)
    if pc:
        return (pc[0], "USD")          # use the MY (MYR) price as-is, tagged USD
    # Fallback: any standalone price on the page.
    try:
        raw = await page.evaluate(r"""
        () => {
          for (const el of document.querySelectorAll('span,div,p,b,strong')) {
            const t = (el.textContent || '').trim().replace(/\s+/g, ' ');
            if (/^(USD|US\$|RM|MYR|\$)\s?\d[\d.,]+$/i.test(t)) return t;
          }
          return null;
        }
        """)
    except Exception:
        raw = None
    if raw:
        pc = parse_price_currency(raw)
        if pc:
            return (pc[0], "USD")
    pc = await generic_extract(page, url, denom)
    return (pc[0], "USD") if pc else None


async def adapter_offgamers(page, url, denom):
    # OffGamers: the offer_id in the URL pre-selects the denomination, so the
    # main price (span.text-h6.text-weight-regular, e.g. "383.50") is that
    # denomination's price. The currency (MYR/USD) sits in the surrounding text.
    try:
        await page.wait_for_selector('span.text-h6', timeout=12000)  # let the SPA render the price
    except Exception:
        pass
    try:
        raw = await page.evaluate(r"""
        () => {
          const pe = document.querySelector('span.text-h6.text-weight-regular')
                  || document.querySelector('span.text-h6');
          if (!pe) return null;
          const val = (pe.textContent || '').replace(/[^0-9.]/g, '');
          if (!val) return null;
          let ctx = pe; for (let i = 0; i < 3 && ctx.parentElement; i++) ctx = ctx.parentElement;
          const t = ctx.textContent || '';
          let cur = 'USD';
          if (/\bRM|\bMYR/i.test(t)) cur = 'MYR';
          else if (/S\$|\bSGD/i.test(t)) cur = 'SGD';
          else if (/€|\bEUR/i.test(t)) cur = 'EUR';
          else if (/£|\bGBP/i.test(t)) cur = 'GBP';
          return cur + ' ' + val;
        }
        """)
    except Exception:
        raw = None
    return parse_price_currency(raw) if raw else await generic_extract(page, url, denom)


# --- G2G via JSON API ------------------------------------------------------
# G2G renders prices client-side from sls.g2g.com (an AWS/CloudFront API that is
# NOT behind the Cloudflare wall on www.g2g.com). The offer/group page calls
#   sls.g2g.com/offer/search?seo_term=<slug>&region_id=<r>&filter_attr=<fa>
#       &sort=lowest_price&currency=USD&country=US&...
# returning JSON offers with converted_unit_price already in USD. We derive that
# URL straight from our catalog URL — no browser, no FX, works on any IP.
import urllib.parse as _uparse


# G2G obfuscates some brand slugs over time (DMCA), e.g. spotify -> sptfy. If the
# stored slug 404s we retry with these swaps so renames self-heal. filter_attr (the
# denomination attribute) stays valid across renames, so only the slug needs fixing.
_G2G_SLUG_ALIASES = [("spotify", "sptfy")]


def g2g_seo_from_url(catalog_url):
    parts = [x for x in _uparse.urlparse(catalog_url).path.split("/") if x]
    if "categories" in parts:
        i = parts.index("categories")
        if i + 1 < len(parts):
            return parts[i + 1]
    return None


def _g2g_seo_candidates(seo):
    cands = [seo]
    for a, b in _G2G_SLUG_ALIASES:
        for x, y in ((a, b), (b, a)):
            if x in seo:
                alt = seo.replace(x, y)
                if alt not in cands:
                    cands.append(alt)
    return cands


def g2g_api_url(catalog_url, seo_override=None):
    """Build the sls.g2g.com price API URL from a /categories/<slug>/offer/group URL."""
    seo = seo_override or g2g_seo_from_url(catalog_url)
    if not seo:
        return None
    q = _uparse.parse_qs(_uparse.urlparse(catalog_url).query)
    params = {"seo_term": seo, "sort": "lowest_price", "page_size": "20",
              "group": "0", "currency": "USD", "country": "US", "v": "v2"}
    if q.get("fa"):
        params["filter_attr"] = q["fa"][0]
    if q.get("region_id"):
        params["region_id"] = q["region_id"][0]
    return "https://sls.g2g.com/offer/search?" + _uparse.urlencode(params)


def _g2g_try(api_url):
    """Return ('ok', price) | ('empty', None) | ('notfound', None) | ('err', None)."""
    import ssl
    import urllib.error
    for ctx in (None, ssl._create_unverified_context()):
        try:
            req = urllib.request.Request(
                api_url, headers={"User-Agent": USER_AGENT, "Accept": "application/json"})
            with urllib.request.urlopen(req, timeout=20, context=ctx) as r:
                data = json.loads(r.read().decode())
            results = (data.get("payload") or {}).get("results") or []
            prices = [o.get("converted_unit_price") for o in results
                      if isinstance(o.get("converted_unit_price"), (int, float))
                      and o.get("converted_unit_price") > 0]
            return ("ok", min(prices)) if prices else ("empty", None)
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return ("notfound", None)   # bad slug -> try an alias
        except Exception:
            pass
    return ("err", None)


def fetch_g2g_price_sync(catalog_url):
    """Call the G2G API, retrying with slug aliases on 404, and return
    (min_usd_price, 'USD'), NA (valid slug but no offers), or None."""
    seo = g2g_seo_from_url(catalog_url)
    if not seo:
        return None
    empty_seen = False
    for cand in _g2g_seo_candidates(seo):
        api = g2g_api_url(catalog_url, seo_override=cand)
        status, val = _g2g_try(api)
        if status == "ok":
            return (val, "USD")
        if status == "empty":
            empty_seen = True   # slug is valid; this denomination is just sold out
    return NA if empty_seen else None


# --- OffGamers via JSON API ------------------------------------------------
# OG renders prices client-side from sls.offgamers.com (AWS/CloudFront, CORS open,
# no Cloudflare wall). The offer_id in our catalog URLs ROTATES over time, so we
# don't rely on it: we look up the product's LIVE offer list by its slug and match
# the denomination by title (e.g. "USDT 50"). converted_unit_price is already USD.
# The old offer_id endpoint is kept only as a fallback. No browser, no FX, any IP.
import ssl as _ssl

# Brand-agnostic denomination matching: we compare DENOMINATION signatures, never
# brand names, so catalog abbreviations (RBL/WOW/DC/Sptfy) match the site's full
# names. A signature = currency code (if any) + unit word (if any) + the set of
# numbers. Longer currency codes first so USDT/USDC win over USD.
_OG_CUR_RE = re.compile(
    r"\b(USDT|USDC|USD|EUR|GBP|JPY|MYR|SGD|AUD|CAD|CNY|TRY|BRL|IDR|PHP|HKD|TWD|KRW|THB|VND)\b", re.I)
_OG_UNIT_RE = re.compile(
    r"\b(day|month|year|diamond|crystal|coin|point|credit|gem|robux|rbx|lunite|genesis|uc|cp)s?\b", re.I)


def _og_sig(text):
    """{'cur','unit','nums'} denomination signature, ignoring brand words."""
    s = (text or "").replace(",", "")
    cm = _OG_CUR_RE.search(s)
    um = _OG_UNIT_RE.search(s)
    nums = set()
    for x in re.findall(r"\d+(?:\.\d+)?", s):
        try:
            nums.add(float(x))
        except ValueError:
            pass
    return {"cur": cm.group(1).upper() if cm else None,
            "unit": um.group(1).lower() if um else None,
            "nums": nums}


def _og_match(want, got):
    """True if two denomination signatures refer to the same denomination."""
    if not want["nums"]:
        return False
    if want["cur"] and got["cur"]:
        # currency cards (e.g. USDT 50): same currency + the amount appears
        return want["cur"] == got["cur"] and bool(want["nums"] & got["nums"])
    # otherwise (subscriptions, time/game cards): same numbers + matching unit
    if want["nums"] != got["nums"]:
        return False
    if want["unit"] and got["unit"] and want["unit"] != got["unit"]:
        return False
    return True


def _og_seo_term(catalog_url):
    parts = [x for x in _uparse.urlparse(catalog_url).path.split("/") if x]
    if "product" in parts:
        i = parts.index("product")
        if i + 1 < len(parts):
            return parts[i + 1]
    return None


def _og_get_json(url):
    for ctx in (None, _ssl._create_unverified_context()):
        try:
            req = urllib.request.Request(
                url, headers={"User-Agent": USER_AGENT, "Accept": "application/json"})
            with urllib.request.urlopen(req, timeout=20, context=ctx) as r:
                return json.loads(r.read().decode())
        except Exception:
            continue
    return None


def _og_collect_offers(obj, out):
    """Walk any OG JSON response and collect denomination entries. OG exposes the
    after-discount price as `raw_final_price` (the `price`/SRP is the strikethrough
    figure). `stock_status` is "buy" when in stock, "out_of_stock" otherwise."""
    if isinstance(obj, dict):
        title = obj.get("title")
        rf = obj.get("raw_final_price")
        if rf is None:
            rf = obj.get("raw_price")
        if isinstance(title, str) and isinstance(rf, (int, float)) and rf > 0:
            out.append({"title": title, "price": float(rf),
                        "stock": str(obj.get("stock_status") or "").lower()})
        for v in obj.values():
            _og_collect_offers(v, out)
    elif isinstance(obj, list):
        for v in obj:
            _og_collect_offers(v, out)


def _og_find_cat_id(obj):
    """Find the legacy numeric category id in an OG JSON payload. search/lite
    offers expose it as `lgc_category_id` (e.g. "5329"); the same id is what
    getProductList?cat_id=<id> needs."""
    if isinstance(obj, dict):
        for k, v in obj.items():
            if k.lower() in ("lgc_category_id", "lgc_cat_id", "cat_id",
                             "category_id", "categories_id", "catid") \
                    and str(v).isdigit():
                return str(v)
        for v in obj.values():
            r = _og_find_cat_id(v)
            if r:
                return r
    elif isinstance(obj, list):
        for v in obj:
            r = _og_find_cat_id(v)
            if r:
                return r
    return None


def fetch_og_price_sync(catalog_url, pname=""):
    """Resolve an OG price by matching the denomination by title and reading its
    DISCOUNTED price (raw_final_price). Chain (verified against the live API):
      1. offer/<offer_id>  -> the legacy numeric category id (lgc_category_id) for
         the correct region. (seo_info has only UUIDs; search/lite without the
         right region_id returns a DIFFERENT region, so we don't rely on it.)
      2. www.offgamers.com/site/getProductList?cat_id=<id>  -> every denomination
         with raw_final_price (after-discount) + stock_status. (This endpoint
         always returns USD; the currency param is ignored.)
    Prefers in-stock offers but still reports a price when out of stock. Returns
    (usd, 'USD') or None."""
    want = _og_sig(pname)
    candidates = []
    cat_id = None
    offer_payload = None

    # 1. cat_id straight from the offer_id in the catalog URL (most reliable).
    q = _uparse.parse_qs(_uparse.urlparse(catalog_url).query)
    oid = q.get("offer_id", [None])[0]
    if oid:
        d = _og_get_json("https://sls.offgamers.com/offer/" + oid + "?"
                         + _uparse.urlencode({"currency": "USD", "country": "US"}))
        offer_payload = (d or {}).get("payload") or {}
        cat_id = _og_find_cat_id(offer_payload)

    # 2. Fallback: resolve cat_id via seo_info -> search/lite.
    if not cat_id:
        seo = _og_seo_term(catalog_url)
        if seo and want["nums"]:
            info = _og_get_json("https://sls.offgamers.com/offer/product/seo_info?"
                                + _uparse.urlencode({"seo_term": seo, "currency": "USD"}))
            p = (info or {}).get("payload") or {}
            sid, bid = p.get("service_id"), p.get("brand_id")
            if sid and bid:
                data = _og_get_json(
                    "https://sls.offgamers.com/offer/search/lite?"
                    + _uparse.urlencode({"service_id": sid, "brand_id": bid,
                                         "country": "US", "currency": "USD"}))
                cat_id = _og_find_cat_id(data)

    # 3. getProductList -> discounted raw_final_price per denomination.
    if cat_id:
        pl = _og_get_json("https://www.offgamers.com/site/getProductList?"
                          + _uparse.urlencode({"cat_id": cat_id}))
        _og_collect_offers(pl, candidates)
    if getattr(ARGS, "debug", False):
        print(f"    [OG-DEBUG] {pname!r} offer_id={oid} cat_id={cat_id} "
              f"candidates={len(candidates)}", flush=True)

    instock, allprices = [], []
    for c in candidates:
        if not _og_match(want, _og_sig(c["title"])):
            continue
        if getattr(ARGS, "debug", False):
            print(f"    [OG-DEBUG] {pname!r} :: {c['title']!r} "
                  f"stock={c['stock']} raw_final_price={c['price']}", flush=True)
        allprices.append(c["price"])
        if c["stock"] in ("buy", "in_stock", "instock", "available", ""):
            instock.append(c["price"])
    if instock:
        return (round(min(instock), 4), "USD")
    if allprices:           # out of stock, but still report the (discounted) price
        return (round(min(allprices), 4), "USD")

    # Last resort: the offer endpoint's own price (this is the SRP, no discount).
    if offer_payload:
        price = offer_payload.get("raw_final_price")
        if not isinstance(price, (int, float)):
            price = offer_payload.get("unit_price_in_usd")
        if not isinstance(price, (int, float)):
            price = offer_payload.get("converted_unit_price")
        if isinstance(price, (int, float)) and price > 0:
            return (round(price, 4), "USD")
    return None


async def adapter_g2g(page, url, denom):
    # G2G offer/group page: our URL already pre-selects denomination (fa=),
    # US region (region_id) and sort=lowest_price, so the featured offer is the
    # cheapest. Its total is in span.text-h6.text-weight-medium ("90.00 USD").
    try:
        await page.wait_for_selector('#pcMain span.text-h6, span.text-h6.text-weight-medium', timeout=12000)
    except Exception:
        pass
    try:
        raw = await page.evaluate(r"""
        () => {
          const pe = document.querySelector('span.text-h6.text-weight-medium')
                  || document.querySelector('#pcMain span.text-h6');
          if (!pe) return null;
          const val = (pe.textContent || '').replace(/[^0-9.]/g, '');
          if (!val) return null;
          let ctx = pe; for (let i = 0; i < 4 && ctx.parentElement; i++) ctx = ctx.parentElement;
          const t = ctx.textContent || '';
          let cur = 'USD';
          if (/\bRM|\bMYR/i.test(t)) cur = 'MYR';
          else if (/S\$|\bSGD/i.test(t)) cur = 'SGD';
          else if (/€|\bEUR/i.test(t)) cur = 'EUR';
          else if (/£|\bGBP/i.test(t)) cur = 'GBP';
          return cur + ' ' + val;
        }
        """)
    except Exception:
        raw = None
    return parse_price_currency(raw) if raw else await generic_extract(page, url, denom)


async def adapter_g2a(page, url, denom):
    # G2A server-renders pricing into the raw HTML. We re-fetch the raw HTML (the
    # page's own session beats Cloudflare, and React strips these blobs from the
    # live DOM after hydration) and read the price from two sources, in order:
    #
    #   1. schema.org JSON-LD AggregateOffer.lowPrice — the cheapest *real* selling
    #      offer for this listing. This is the number we record. NOTE: do NOT use
    #      `suggestedPrice` / `highPrice` — those are G2A's strikethrough SRP, not a
    #      price anyone pays (it runs ~$8-9 above the real low and would make G2A
    #      look uncompetitive).
    #   2. Fallback: walk sections.data[*].data.offers in the
    #      <script type="application/json+redux"> blob and take the lowest
    #      prices.normal.price (the buyer total).
    #
    # app.currency / priceCurrency gives the currency for conversion. Each G2A URL
    # is one denomination, so the cheapest offer is that denomination's price.
    try:
        res = await page.evaluate(r"""
        async () => {
          let html;
          try { const r = await fetch(location.href, {headers: {'Accept': 'text/html'}}); html = await r.text(); }
          catch (e) { html = document.documentElement.outerHTML; }

          // 1. schema.org AggregateOffer.lowPrice (primary).
          const lds = [...html.matchAll(/<script type="application\/ld\+json">([\s\S]*?)<\/script>/g)];
          for (const ld of lds) {
            let obj; try { obj = JSON.parse(ld[1]); } catch (e) { continue; }
            const nodes = Array.isArray(obj) ? obj : [obj];
            for (const node of nodes) {
              const offers = node && node.offers;
              const offs = Array.isArray(offers) ? offers : (offers ? [offers] : []);
              for (const off of offs) {
                const lp = Number(off && off.lowPrice);
                if (!isNaN(lp) && lp > 0) {
                  return { price: lp, currency: (off.priceCurrency || 'USD') };
                }
              }
            }
          }

          // 2. redux offers walk (fallback).
          const m = html.match(/<script type="application\/json\+redux">([\s\S]*?)<\/script>/);
          if (!m) return null;
          let j; try { j = JSON.parse(m[1]); } catch (e) { return null; }
          const data = (j.sections || {}).data || {};
          const prices = [];
          for (const k of Object.keys(data)) {
            const co = data[k];
            const offers = co && co.data && co.data.offers;
            if (!offers) continue;
            for (const o of offers) {
              const p = o && o.prices && o.prices.normal && o.prices.normal.price;
              const n = Number(p);
              if (!isNaN(n) && n > 0) prices.push(n);
            }
          }
          if (!prices.length) return null;
          return { price: Math.min(...prices), currency: (j.app && j.app.currency) || 'USD' };
        }
        """)
    except Exception:
        res = None
    if res and isinstance(res.get("price"), (int, float)) and res["price"] > 0:
        return (round(float(res["price"]), 2), (res.get("currency") or "USD").upper())

    # Fallback: featured-offer price from the live DOM, then generic text scan.
    try:
        await page.wait_for_selector('[class*="text-price-3xl"]', timeout=6000)
    except Exception:
        pass
    try:
        raw = await page.evaluate(r"""
        () => {
          const btn = [...document.querySelectorAll('button,a')]
            .find(b => /add to cart/i.test(b.textContent || ''));
          if (btn) {
            let node = btn;
            for (let i = 0; i < 8 && node; i++) {
              const pe = node.querySelector && node.querySelector('[class*="text-price-3xl"],[class*="text-price-2xl"]');
              if (pe && pe.textContent.trim()) return pe.textContent.trim();
              node = node.parentElement;
            }
          }
          const pe = document.querySelector('[class*="text-price-3xl"]');
          return pe ? pe.textContent.trim() : null;
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
    "offgamers.com": adapter_offgamers,
    "g2g.com": adapter_g2g,
    "g2a.com": adapter_g2a,
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
    # SEAGM prices are region-specific: a slug with no locale redirects to the
    # visitor's geo locale (e.g. /en-my/ -> cheaper MYR pricing). Force /en-us/ so
    # we always read the US/USD prices, consistent with the other competitors.
    host = urlparse(url).netloc.replace("www.", "").lower()
    if host.endswith("seagm.com"):
        p = urlparse(url)
        parts = [x for x in p.path.split("/") if x]
        if parts and re.fullmatch(r"[a-z]{2}-[a-z]{2}", parts[0]):
            parts[0] = "en-us"               # replace existing locale
        else:
            parts = ["en-us"] + parts        # insert locale
        return p._replace(path="/" + "/".join(parts)).geturl()
    return url


# --- fetching ---------------------------------------------------------------
async def fetch_one(context, task, results, report):
    url, comp = task["url"], task["comp"]
    fn = adapter_for(url)

    # G2G: skip the browser entirely and read the JSON price API. Fast, USD-native,
    # and works on datacenter IPs (sls.g2g.com isn't Cloudflare-walled). Falls
    # through to the Playwright DOM adapter below only if the API yields nothing.
    host = urlparse(url).netloc.replace("www.", "").lower()
    is_api = host.endswith("g2g.com") or host.endswith("offgamers.com")
    if is_api:
        try:
            loop = asyncio.get_event_loop()
            if host.endswith("g2g.com"):
                pc = await loop.run_in_executor(None, fetch_g2g_price_sync, url)
            else:
                pc = await loop.run_in_executor(None, fetch_og_price_sync, url, task["pname"])
        except Exception:
            pc = None
        if pc == NA:
            results.setdefault(task["sheet"], {}).setdefault(task["pname"], {})[comp] = NA
            report["ok"] += 1
            return
        if pc:
            usd = to_usd(pc[0], pc[1])
            if usd is not None and usd > 0:
                results.setdefault(task["sheet"], {}).setdefault(task["pname"], {})[comp] = usd
                report["ok"] += 1
                return

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
            # Fold in the per-competitor note (the site-specific denomination
            # label, e.g. "7740 Diamonds + 1548 Bonus") so matching works when
            # the site labels by base+bonus while our catalog uses the total.
            note = task.get("note")
            if note:
                nd = parse_denomination(note)
                merged_nums = []
                for n in (nd["nums"] or []) + (denom["nums"] or []):
                    if n not in merged_nums:
                        merged_nums.append(n)
                denom["nums"] = merged_nums
                merged_words = []
                for w in (denom["words"] or []) + (nd["words"] or []):
                    if w not in merged_words:
                        merged_words.append(w)
                denom["words"] = merged_words
                if denom.get("amount") is None and nd.get("amount") is not None:
                    denom["amount"] = nd["amount"]
            result = await fn(page, url, denom)   # (value, currency), NA, or None
            # Sold-out guard: if no confident price came back, check whether the
            # page says the item is unavailable -> record N/A instead of nothing
            # (and avoid a misleading number from a fallback).
            if result is None or result == NA:
                try:
                    body = await page.inner_text("body")
                except Exception:
                    body = ""
                if looks_sold_out(body):
                    result = NA
            await page.close()
            if result == NA:
                results.setdefault(task["sheet"], {}).setdefault(task["pname"], {})[comp] = NA
                report["ok"] += 1
                return
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
    # No price detected after all attempts -> record N/A rather than leaving the
    # cell blank (applies to every site). The dashboard auto-replaces N/A with a
    # real price on the next successful run.
    results.setdefault(task["sheet"], {}).setdefault(task["pname"], {})[comp] = NA
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
# (All current competitors have adapters; this stays as an easy kill-switch.)
SKIP_COMPS = set()


def build_tasks(data, only_categories, limit, only_comps=None, skip_comps=None):
    tasks = []
    for cat, block in data["categories"].items():
        if only_categories and cat not in only_categories:
            continue
        for product in block["products"]:
            for comp, info in product["urls"].items():
                if comp in SKIP_COMPS:
                    continue
                if only_comps and comp not in only_comps:
                    continue
                if skip_comps and comp in skip_comps:
                    continue
                tasks.append({"sheet": cat, "pname": product["name"],
                              "comp": comp, "url": info["url"], "note": info.get("note")})
    return tasks[:limit] if limit else tasks


def main():
    if not URLS_FILE.exists():
        sys.exit(f"Missing {URLS_FILE} — generate it from the products spreadsheet first.")
    data = json.loads(URLS_FILE.read_text(encoding="utf-8"))

    only = set(c.strip() for c in ARGS.categories.split(",")) if ARGS.categories else None
    only_comps = set(c.strip() for c in ARGS.comps.split(",")) if ARGS.comps else None
    skip_comps = set(c.strip() for c in ARGS.skip_comps.split(",")) if ARGS.skip_comps else None
    tasks = build_tasks(data, only, ARGS.limit, only_comps, skip_comps)
    if ARGS.debug:
        DEBUG_DIR.mkdir(exist_ok=True)
    print(f"Scraping {len(tasks)} URLs across "
          f"{len(only) if only else len(data['categories'])} categories"
          f"{' [DEBUG]' if ARGS.debug else ''}…", flush=True)

    t0 = time.time()
    results, report = asyncio.run(run(tasks))

    if ARGS.merge and OUT_FILE.exists():
        # Patch this run's comps into the existing prices.json instead of
        # overwriting it. Lets a local OG/G2G run coexist with the cloud run.
        try:
            prev = json.loads(OUT_FILE.read_text(encoding="utf-8"))
            base = prev.get("prices", {}) if isinstance(prev, dict) else {}
        except Exception:
            base = {}
        scraped_comps = {t["comp"] for t in tasks}
        # drop stale entries for the comps we just re-scraped, then overlay
        for sheet, prods in list(base.items()):
            for pname, comps in list(prods.items()):
                for c in list(comps.keys()):
                    if c in scraped_comps:
                        del comps[c]
        for sheet, prods in results.items():
            for pname, comps in prods.items():
                base.setdefault(sheet, {}).setdefault(pname, {}).update(comps)
        # prune any now-empty product/sheet dicts
        for sheet in list(base.keys()):
            for pname in list(base[sheet].keys()):
                if not base[sheet][pname]:
                    del base[sheet][pname]
            if not base[sheet]:
                del base[sheet]
        results = base

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
    ap.add_argument("--comps", default="", help="only these competitors, e.g. 'OG,G2G'")
    ap.add_argument("--skip-comps", dest="skip_comps", default="",
                    help="skip these competitors, e.g. 'OG,G2G' (for the cloud run)")
    ap.add_argument("--merge", action="store_true",
                    help="patch this run's comps into existing prices.json instead of overwriting")
    ap.add_argument("--limit", type=int, default=0, help="cap total fetches (smoke test)")
    ap.add_argument("--headful", action="store_true", help="show the browser window")
    ap.add_argument("--debug", action="store_true", help="save screenshots + findings.json per URL")
    ARGS = ap.parse_args()
    main()
