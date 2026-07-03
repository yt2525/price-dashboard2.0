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
from urllib.parse import urlparse, urljoin, quote_plus

from playwright.async_api import async_playwright

ROOT = Path(__file__).resolve().parent
URLS_FILE = ROOT / "urls.json"
CUSTOM_FILE = ROOT / "custom_products.json"   # user-added products (dashboard export)
BRAND_URLS_FILE = ROOT / "brand_urls.json"    # one product-page URL per brand+competitor
OUT_FILE = ROOT / "prices.json"
HISTORY_FILE = ROOT / "price_history.json"   # daily snapshots for the date picker
HISTORY_DAYS = 180                           # keep ~6 months of daily snapshots
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
  let label = null, bestScore = 0, bestLen = 1e9, bestNum = -1;
  for (const el of document.querySelectorAll('div,span,li,a,p,button,label,td,h1,h2,h3,h4')) {
    const t = (el.textContent || '').replace(/,/g, '');
    if (t.length > 90) continue;
    const tl = t.toLowerCase();
    // numScore counts matched target numbers, counting BOTH a direct number
    // match AND base+bonus pairs whose SUM equals a target total (sites often
    // label "7740 Diamonds + 1548 Bonus" for a 9288 total). maxNum is the LARGEST
    // matched target so we prefer the real total over a smaller sub-number.
    const _hit = new Set();
    for (let i = 0; i < numRes.length; i++) if (numRes[i].test(t)) _hit.add(nums[i]);
    {
      const cn = (t.replace(/(US\$|USD|RM|MYR|S\$|SGD|€|£|\$)\s?\d[\d.]*/gi, ' ').match(/\d+/g) || [])
                   .map(Number).filter(x => x > 0);
      for (let a = 0; a < cn.length; a++) for (let b = a + 1; b < cn.length; b++)
        if (nums.indexOf(cn[a] + cn[b]) !== -1) _hit.add(cn[a] + cn[b]);
    }
    let numScore = _hit.size, maxNum = -1; for (const n of _hit) if (n > maxNum) maxNum = n;
    let wordScore = 0; for (const w of ws) if (tl.includes(w)) wordScore++;
    const score = numScore * 10 + wordScore;
    if (score === 0) continue;
    // numbered denomination -> require a real number match; never match on words
    // alone, which would grab an unrelated card when our size isn't offered.
    if (numRes.length && numScore === 0) continue;
    // accept titles via the keyword gate, OR any element that hit a name-word
    if (!GATE.test(t) && wordScore === 0) continue;
    if (score > bestScore ||
        (score === bestScore && maxNum > bestNum) ||
        (score === bestScore && maxNum === bestNum && t.length < bestLen)) {
      label = el; bestScore = score; bestLen = t.length; bestNum = maxNum;
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


_SEAGM_JS = r"""
(args) => {
  const nums = args.nums || [], words = (args.words || []).map(w => w.toLowerCase());
  const numRes = nums.map(n => new RegExp('(?<![\\d.])' + n + '(?![\\d.])'));
  const scoreName = (name) => {
    const nm = (name || '').replace(/,/g, '');
    // Count a direct number match AND base+bonus pairs whose SUM equals a tracked
    // total (e.g. "7740 + 1548 Diamonds" -> 9288); each counted number scores 10.
    const hit = new Set();
    for (let i = 0; i < numRes.length; i++) if (numRes[i].test(nm)) hit.add(nums[i]);
    const cn = (nm.replace(/(US\$|USD|RM|MYR|S\$|SGD|€|£|\$)\s?\d[\d.]*/gi, ' ').match(/\d+/g) || [])
                 .map(Number).filter(x => x > 0);
    for (let a = 0; a < cn.length; a++) for (let b = a + 1; b < cn.length; b++)
      if (nums.indexOf(cn[a] + cn[b]) !== -1) hit.add(cn[a] + cn[b]);
    let s = hit.size * 10;
    const nl = nm.toLowerCase(); for (const w of words) if (nl.includes(w)) s += 1;
    return s;
  };

  // ---- PRIMARY: the embedded clientData "API" ----
  // window.clientData.cardTypeList[id] holds each denomination's unit_price (the
  // pre-discount price in the DISPLAY currency) + card_count (stock). The real
  // selling price = unit_price * (1 - rebate/100), where rebate is the cardRuleList
  // discount for that id (this reproduces the orange DOM price exactly, e.g. PSN
  // 100: 100 * (1 - 8.5%) = 91.50). Only trust it when the page is USD
  // (currency_format contains "US$", which the /en-us/ locale guarantees).
  try {
    const cd = window.clientData;
    if (cd && cd.cardTypeList) {
      if (!/US\$/.test(cd.currency_format || '')) return { nonUsd: true };
      const list = Array.isArray(cd.cardTypeList) ? cd.cardTypeList : Object.values(cd.cardTypeList);
      const rules = cd.cardRuleList || {};
      let best = null, bestScore = 0, bestLen = 1e9;
      for (const c of list) {
        const name = c.name || c.name_us || '';
        const s = scoreName(name);
        if (numRes.length && s < 10) continue;
        if (s === 0) continue;
        const base = parseFloat(c.unit_price);
        if (!(base > 0)) continue;
        let rebate = parseFloat(c.discount_rate) || 0;
        const rl = rules[c.id] || rules[String(c.id)] || [];
        for (const r of (Array.isArray(rl) ? rl : [])) {
          if (r.type === 'discount' && parseFloat(r.rebate) > rebate) rebate = parseFloat(r.rebate);
        }
        const price = +(base * (1 - rebate / 100)).toFixed(2);
        const inStock = (Number(c.card_count) > 0) || !!Number(c.is_ordering);
        const sc = s + (inStock ? 100 : 0);
        if (sc > bestScore || (sc === bestScore && name.length < bestLen)) {
          best = { price: price }; bestScore = sc; bestLen = name.length;
        }
      }
      if (best) return best;
    }
  } catch (e) {}

  // ---- FALLBACK: read the orange discounted <b> from the SKU_type DOM ----
  const parseUsd = el => {
    if (!el) return null;
    const t = (el.textContent || '').replace(/,/g, '');
    if (!/US\$/i.test(t)) return { nonUsd: true };
    const m = t.match(/US\$\s*(\d+(?:\.\d+)?)/i);
    return m ? { price: parseFloat(m[1]) } : null;
  };
  let best = null, bestScore = 0, bestLen = 1e9, sawNonUsd = false;
  for (const c of [...document.querySelectorAll('div.SKU_type')]) {
    const full = (c.innerText || '').replace(/\s+/g, ' ').trim();
    const name = full.split(/US\$/i)[0].replace(/,/g, '').trim();
    const s = scoreName(name);
    if (numRes.length && s < 10) continue;
    if (s === 0) continue;
    const pe = c.querySelector('.price b:not(.price_origional)') || c.querySelector('.price b');
    const pr = parseUsd(pe);
    if (pr && pr.nonUsd) { sawNonUsd = true; continue; }
    if (!pr || !pr.price) continue;
    if (s > bestScore || (s === bestScore && name.length < bestLen)) {
      best = { price: pr.price }; bestScore = s; bestLen = name.length;
    }
  }
  return best || (sawNonUsd ? { nonUsd: true } : null);
}
"""


async def adapter_seagm(page, url, denom):
    # Match the denomination card (div.SKU_type) by number + name and read the
    # ORANGE discounted USD price directly. SEAGM is pinned to USD for the run
    # (see seagm_force_usd) and the site prints US$ natively, so we NEVER use the
    # currency converter — we return the on-page US$ figure as-is. If no US$ price
    # is present (denom missing or session not USD), return None so fetch_one's
    # sold-out check records N/A rather than a converted/guessed number.
    try:
        res = await page.evaluate(_SEAGM_JS, {"nums": denom.get("nums") or [],
                                              "words": denom.get("words") or []})
    except Exception:
        res = None
    if res and res.get("price"):
        return (res["price"], "USD")
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
  // Detect a denomination GRID: many short "<number> <CUR>" face-value cards
  // (e.g. "45.50 USD", "200 QAR"). If the page has a grid but our denomination
  // isn't one of the cards, the product simply isn't offered in that size -> N/A
  // (do NOT fall back to a page-wide price scan, which would grab an unrelated
  // amount). Single-offer pages (no grid) keep the old fallback behaviour.
  const faces = new Set();
  for (const el of document.querySelectorAll('div,span,button,label')) {
    const t = (el.textContent || '').replace(/\s+/g, ' ').trim();
    // Allow thousands separators so comma-formatted grids (e.g. "10,000 IDR",
    // "1,000,000 IDR") are recognised. Without this, IDR/large-value grids look
    // like non-grid pages and the gridNoMatch -> N/A guard never fires, letting a
    // page-wide price scan grab an unrelated amount.
    if (t.length < 18 && /^\d[\d.,]*\s*[A-Z]{2,4}$/.test(t)) faces.add(t);
    // Also recognise unit/diamond grids: "706 Diamonds", "5250 + 1350 Diamonds",
    // "60 UC", "1000 CP", "500 Points". Without this, diamond grids look like
    // single-offer pages and the gridNoMatch -> N/A guard never fires.
    if (t.length < 40 &&
        /^\d[\d.,]*(\s*\+\s*\d[\d.,]*)?\s*([A-Za-z]+\s+)?(Diamonds?|Bonus|Points?|Coins?|Gems?|Crystals?|Shards?|Lunites?|UC|CP|Tokens?)\b/i.test(t))
      faces.add(t);
  }
  const hasGrid = faces.size >= 5;
  // Collect EVERY short element whose face value matches (the grid card title AND
  // the "Value:" header both say e.g. "150 CAD"). We try them all below, because
  // only the grid card has the price next to it.
  const labels = [];
  for (const el of document.querySelectorAll('div,span,li,a,p,button,label,h1,h2,h3,h4')) {
    const t = (el.textContent || '').replace(/,/g, '');
    if (t.length > 40) continue;                 // card titles are short
    // Match a direct number AND base+bonus pairs whose SUM equals a tracked total
    // (Eneba labels MLBB cards "7740 + 1548 Diamonds" for a tracked 9288 total).
    const hit = new Set();
    for (let i = 0; i < numRes.length; i++) if (numRes[i].test(t)) hit.add(nums[i]);
    {
      const cn = (t.replace(/\$\s?\d[\d.]*/g, ' ').match(/\d+/g) || [])
                   .map(Number).filter(x => x > 0);
      for (let a = 0; a < cn.length; a++) for (let b = a + 1; b < cn.length; b++)
        if ((nums || []).indexOf(cn[a] + cn[b]) !== -1) hit.add(cn[a] + cn[b]);
    }
    let s = hit.size;
    if (numRes.length && s === 0) continue;
    const hasCur = curRe ? curRe.test(t) : false;
    if (hasCur) s += 1;                          // currency match is a strong signal
    labels.push({ el, score: s, len: t.length, hasCur });
  }
  if (!labels.length) return hasGrid ? { gridNoMatch: true } : null;
  // When the page is a denomination grid AND we know the face currency (e.g. GBP),
  // restrict to cards whose title carries that currency ("25 GBP"). This pins us to
  // the correct denomination card and ignores stray featured/buy-box prices (e.g. a
  // "$16.06" seller offer) that would otherwise be picked up. We only apply this
  // filter when at least one currency-matched card exists, so pages that label cards
  // by number alone (or by "$") still match.
  let pool = labels;
  if (hasGrid && curRe) {
    const withCur = labels.filter(l => l.hasCur);
    if (withCur.length) pool = withCur;
  }
  pool.sort((a, b) => b.score - a.score || a.len - b.len);   // best candidates first
  // For every matching card, climb to its OWN small container and read the $ buyer
  // prices, keeping the LOWEST. We scan ALL matching cards and return the global
  // minimum, i.e. the cheapest offer for this exact denomination. PRICE WINS even if
  // the product is sold out. The price regex stops after 2 decimals so "$118.12"
  // next to the "1.27 per $1" ratio isn't misread as 118.121.
  const soldRe = /sold\s*out|out of stock|currently unavailable|temporarily unavailable|notify me|sorry/i;
  const priceRe = /\$\s?(\d[\d,]*(?:\.\d{1,2})?)/g;
  let sold = false, best = null;
  for (const { el } of pool) {
    let node = el;
    for (let i = 0; i < 5 && node; i++) {
      const txt = node.textContent || '';
      if (txt.length < 160) {
        // Drop the "0.71 GBP per $1" exchange-ratio reference so its "$1" isn't
        // mistaken for a $1 buyer price when we take the minimum.
        const clean = txt.replace(/per\s*\$\s*\d[\d.]*/gi, ' ');
        const vals = [...clean.matchAll(priceRe)]
          .map(m => parseFloat(m[1].replace(/,/g, ''))).filter(v => !isNaN(v) && v > 0);
        if (vals.length) { const lo = Math.min(...vals); if (best === null || lo < best) best = lo; break; }
      }
      if (soldRe.test(txt) && txt.length < 200) sold = true;
      node = node.parentElement;
    }
  }
  if (best !== null) return { price: best };
  if (sold) return { soldout: true };
  if (hasGrid) return { gridNoMatch: true };   // grid page, denomination absent -> N/A
  return null;
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
        if res.get("gridNoMatch"):
            # Page has a denomination grid but our size isn't offered -> N/A.
            # Skip the single-offer fallback (it would grab an unrelated price).
            return NA
    # NUMBERED denomination that produced no card/label match above: our exact
    # size isn't on this page (e.g. MLBB "6,000 Diamonds" isn't a real pack, so it
    # matches no card). Do NOT run the single-offer fallback below -- on a
    # denomination page that grabs a stray featured price (e.g. $1.87 from an
    # unrelated pack). The label path already handles legit single-product numbered
    # pages (the number is in the title), so reaching here means the size is absent.
    if denom.get("nums"):
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
                // count a direct number match AND base+bonus pairs whose SUM equals
                // a tracked total (e.g. "7740 Diamonds + 1548 Bonus" -> 9288).
                const hit = new Set();
                for (let i = 0; i < numRes.length; i++) if (numRes[i].test(at)) hit.add(nums[i]);
                const cn = (at.match(/\d+/g) || []).map(Number).filter(x => x > 0);
                for (let a = 0; a < cn.length; a++) for (let b = a + 1; b < cn.length; b++)
                  if ((nums || []).indexOf(cn[a] + cn[b]) !== -1) hit.add(cn[a] + cn[b]);
                const sc = hit.size;
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
    # Numbered denomination with no matching variation -> our size isn't offered.
    # Return N/A rather than a page-wide lowest price (an unrelated denomination).
    if nums:
        return NA
    return await generic_extract(page, url, denom)


_KINGUIN_JS = r"""
() => {
  // Kinguin embeds the full product/offer state in window._preloadedState (a
  // Redux preload), so the price is available without scraping the DOM or
  // hitting a Cloudflare-walled API. The product/denomination is pinned by the
  // categoryId in the URL, so the page's own lowestPrice IS this denomination's
  // cheapest offer (same idea as G2G's min over offers). unitPrice is in cents.
  const s = window._preloadedState;
  if (!s) return null;
  const off = s.offers || {};
  const cur = (s.currencies && s.currencies.current && s.currencies.current.code) || 'USD';
  let price = null;
  if (typeof off.lowestPrice === 'number' && off.lowestPrice > 0) {
    price = off.lowestPrice;
  } else if (off.mainOffer && Number(off.mainOffer.unitPrice) > 0) {
    price = Number(off.mainOffer.unitPrice) / 100;  // unitPrice is in cents
  }
  const oos = !!off.outOfStock || (off.totalElements === 0);
  return { price: price, currency: cur, oos: oos };
}
"""


async def adapter_kinguin(page, url, denom):
    # PRIMARY: the price Kinguin actually DISPLAYS for the main offer. This is what
    # the customer pays and INCLUDES Kinguin's service fee. The embedded
    # _preloadedState.unitPrice is the pre-fee figure (e.g. 429.36 vs the shown
    # 509.61), so the rendered DOM price is the correct one to record. The URL's
    # categoryId pins the exact product, so main-offer = this denomination.
    for sel in ['[data-test="main-offer__price"]',
                '[data-test="main-offer__price-section"]',
                '[data-test*="price-section"]', '[data-test*="price"]']:
        try:
            el = await page.query_selector(sel)
            if el:
                pc = parse_price_currency(await el.inner_text())
                if pc and pc[0] > 0:
                    return pc
        except Exception:
            pass
    # FALLBACK: the embedded state (pre-fee, but better than N/A); also flags OOS.
    try:
        data = await page.evaluate(_KINGUIN_JS)
    except Exception:
        data = None
    if data:
        if isinstance(data.get("price"), (int, float)) and data["price"] > 0:
            return (round(float(data["price"]), 4), data.get("currency") or "USD")
        if data.get("oos"):
            return NA
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
  let label = null, bestScore = 0, bestLen = 1e9, bestNum = -1;
  for (const el of document.querySelectorAll('div,span,li,a,p,button,label,td,h1,h2,h3,h4')) {
    const t = (el.textContent || '').replace(/,/g, '');
    if (t.length > 90) continue;
    const tl = t.toLowerCase();
    // numScore counts matched target numbers, counting BOTH a direct number
    // match AND base+bonus pairs whose SUM equals a target total (sites label
    // "7740 Diamonds + 1548 Bonus" for a tracked 9288 total).
    const _hit = new Set();
    for (let i = 0; i < numRes.length; i++) if (numRes[i].test(t)) _hit.add(nums[i]);
    {
      const cn = (t.replace(/(US\$|USD|RM|MYR|S\$|SGD|€|£|\$)\s?\d[\d.]*/gi, ' ').match(/\d+/g) || [])
                   .map(Number).filter(x => x > 0);
      for (let a = 0; a < cn.length; a++) for (let b = a + 1; b < cn.length; b++)
        if (nums.indexOf(cn[a] + cn[b]) !== -1) _hit.add(cn[a] + cn[b]);
    }
    let numScore = _hit.size, maxNum = -1; for (const n of _hit) if (n > maxNum) maxNum = n;
    let wordScore = 0; for (const w of ws) if (tl.includes(w)) wordScore++;
    const score = numScore * 10 + wordScore;
    if (score === 0) continue;
    // numbered denomination -> require a real number match; never match on words
    // alone, which would grab an unrelated card when our size isn't offered.
    if (numRes.length && numScore === 0) continue;
    if (!GATE.test(t) && wordScore === 0) continue;
    if (score > bestScore || (score === bestScore && maxNum > bestNum) ||
        (score === bestScore && maxNum === bestNum && t.length < bestLen)) {
      label = el; bestScore = score; bestLen = t.length; bestNum = maxNum;
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
    # Numbered denomination: if we couldn't match the card (or it had no price),
    # our size isn't offered here -> N/A. Never fall back to a page-wide lowest
    # price, which would report an unrelated denomination's price.
    if denom.get("nums"):
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
    # Numbered denomination not matched on the grid -> our size isn't offered
    # here. Return N/A rather than grabbing an unrelated denomination's price.
    if denom.get("nums"):
        return NA
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


def og_search_seo(query, denom):
    """OG name-search: query OG's keyword-search API, pick the result whose brand
    name matches, and return an /product/<seo_term> URL that fetch_og_price_sync
    can price (it then matches the denomination by title). Returns a URL or None.

    NB: OG's search is fuzzy (it returns e.g. 'Age of Empires' for an unknown
    term), so we word-gate via _pick_best — an unmatched brand yields N/A. We
    query by BRAND WORDS only ("gate io", "steam wallet"): the denomination/
    currency and punctuation (e.g. the '.' in gate.io) break OG's matcher."""
    brand = " ".join(denom.get("words") or [])
    api = ("https://sls.offgamers.com/offer/keyword/search?"
           + _uparse.urlencode({"q": brand or query, "root_id": "all",
                                 "user_country": "US", "page_size": 50}))
    d = _og_get_json(api)
    results = ((d or {}).get("payload") or {}).get("results") or []
    cands = [{"text": r.get("default_name") or "", "seo_term": r.get("seo_term")}
             for r in results if r.get("seo_term")]
    best = _pick_best(cands, denom, "family")
    if not best:
        return None
    return "https://www.offgamers.com/product/" + best["seo_term"]


# --- G2G name-search (no stored URL) --------------------------------------
# G2G's keyword index only has BRAND slugs, but the sellable listing is a
# CATEGORY (e.g. brand "riot-points" -> category "riot-points-gift-cards") and
# the denomination is an opaque fa hash. Rather than resolve that hash, we use
# the fact that offer TITLES carry the denomination + region ("Riot Points Gift
# Card USD 50 (US)") — exactly like OG. So: find the category in categories.json
# by brand name, scope offers to the product's region, then match the
# denomination by title. (All verified live against riot-points-gift-cards.)
_G2G_CATS = None


def _g2g_categories():
    global _G2G_CATS
    if _G2G_CATS is None:
        _G2G_CATS = _og_get_json("https://assets.g2g.com/offer/categories.json") or {}
    return _G2G_CATS


_G2G_TOK_STOP = {"gift", "card", "cards", "code", "codes", "voucher", "key", "keys",
                 "top", "up", "global", "the", "for"}
_G2G_CUR_TOK = re.compile(
    r"\b(usd|usdt|usdc|eur|gbp|jpy|cny|cad|myr|rm|sgd|qar|aud|try|brl|idr|php|hkd|twd|krw|thb|vnd)\b")


def _g2g_brand_tokens(name):
    """Brand tokens for matching a G2G category title. Unlike denom_words this is
    only used for the category lookup; we keep it tight and match on word
    boundaries so 'riot' doesn't match 'Marriott'."""
    s = _G2G_CUR_TOK.sub(" ", re.sub(r"\([^)]*\)", " ", name.lower()))
    return [t for t in re.findall(r"[a-z]+", s) if len(t) >= 2 and t not in _G2G_TOK_STOP]


def _g2g_find_category(name):
    """Match the product's brand tokens against categories.json marketing titles
    (whole-word); return the best category seo_term (dict key) or None."""
    toks = _g2g_brand_tokens(name)
    if not toks:
        return None
    res = [re.compile(r"\b" + re.escape(t) + r"\b") for t in toks]
    best, best_score, best_len = None, 0, 10 ** 9
    for key, v in _g2g_categories().items():
        if not isinstance(v, dict):
            continue
        title = ((v.get("marketing_title") or {}).get("en") or "").lower()
        if not title:
            continue
        s = sum(1 for rx in res if rx.search(title))
        if s and (s > best_score or (s == best_score and len(title) < best_len)):
            best, best_score, best_len = key, s, len(title)
    return best


def _g2g_region_id(seo_term, region):
    """Resolve a category's region_id for the product's region (e.g. 'US')."""
    if not region:
        return None
    d = _og_get_json("https://sls.g2g.com/offer/keyword_relation/region?"
                     + _uparse.urlencode({"seo_term": seo_term, "country": "US",
                                          "include_localization": 0}))
    for it in (((d or {}).get("payload") or {}).get("results") or []):
        if (it.get("country_code") or "").upper() == region.upper():
            return it.get("region_id")
    return None


def fetch_g2g_search(query, denom):
    """G2G name-search: brand -> category -> region-scoped offers -> match the
    denomination by title -> cheapest USD price. Returns a float or None."""
    seo = _g2g_find_category(query)
    if not seo:
        return None
    want = _og_sig(query)
    if not want["nums"]:
        return None
    params = {"seo_term": seo, "sort": "lowest_price", "page_size": "50",
              "group": "1", "currency": "USD", "country": "US", "v": "v2"}
    region_id = _g2g_region_id(seo, denom.get("region"))
    if region_id:
        params["region_id"] = region_id
    d = _og_get_json("https://sls.g2g.com/offer/search?" + _uparse.urlencode(params))
    res = ((d or {}).get("payload") or {}).get("results") or []
    prices = [o.get("converted_unit_price") for o in res
              if _og_match(want, _og_sig(o.get("title") or ""))
              and isinstance(o.get("converted_unit_price"), (int, float))
              and o.get("converted_unit_price") > 0]
    return round(min(prices), 4) if prices else None


# Competitors searched via their JSON API (no browser) rather than the DOM. The
# resolver returns a product URL (str, priced later by the adapter) OR a final
# USD price (number, used directly), OR None for no match.
API_SEARCH = {"OG": og_search_seo, "G2G": fetch_g2g_search}


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


# ---------------------------------------------------------------------------
# Name-search fallback: when a product has NO stored URL for a competitor, we
# search that marketplace by product name, pick the result whose denomination
# (and, where possible, region) matches, then price the resolved product page
# with that site's normal adapter. Only competitors listed here participate
# (CLI --search-comps controls which run; G2A is the verified one).
# ---------------------------------------------------------------------------
SEARCH_SITES = {
    # ---- "denom" sites: each denomination is its own listing (number in title) ----
    # VERIFIED against live search pages.
    "G2A": {
        "domain":  "g2a.com", "mode": "denom",
        "search":  lambda q: "https://www.g2a.com/search?query=" + quote_plus(q),
        "link_re": r"-i\d{6,}$",                 # product slugs end in -i<digits>
    },
    "Kinguin": {
        "domain":  "kinguin.net", "mode": "denom",
        "search":  lambda q: "https://www.kinguin.net/listing?phrase=" + quote_plus(q),
        "link_re": r"/category/\d+/",             # /category/<id>/<slug>
    },
    # BEST-EFFORT (search URL confirmed; result-link pattern is broad). Non-matches
    # fall back to N/A thanks to the denomination gate, so a loose pattern is safe.
    "Eneba": {
        "domain":  "eneba.com", "mode": "denom",
        "search":  lambda q: "https://www.eneba.com/store/all?text=" + quote_plus(q),
        "link_re": r"^/[a-z0-9]+(?:-[a-z0-9]+){3,}$",   # long hyphenated product slug
    },
    # ---- "family" sites: one product page per brand + a denomination selector ----
    # We resolve to the product page; the site's adapter then picks the matching
    # denomination. Matched by brand name (denomination number not in the result).
    # VERIFIED against live search pages.
    "Seagm": {
        "domain":  "seagm.com", "mode": "family",
        "search":  lambda q: "https://www.seagm.com/search?keywords=" + quote_plus(q),
        "link_re": r"^/[a-z0-9]+(?:-[a-z0-9]+)+$",      # region-less product slug
    },
    "MooGold": {
        "domain":  "moogold.com", "mode": "family",
        "search":  lambda q: "https://moogold.com/?post_type=product&s=" + quote_plus(q),
        "link_re": r"^/product/",
    },
    # ---- interactive (JS autocomplete, no query URL) ----
    # Codashop: region-specific store; open the header search, type, click a
    # suggestion. Product pages are /en-XX/<slug> or /product/<slug>; the page
    # has a denomination selector that adapter_codashop reads. From the recorded
    # codegen: header-search button + search-input test ids.
    "Codashop": {
        "domain":   "codashop.com", "mode": "family", "interactive": True,
        "store":    lambda denom: "https://www.codashop.com/" + _coda_region(denom) + "/",
        "open_sel": '[data-testid="header-search"] button',
        "input_sel": '[data-testid="search-input-widget"] [data-testid="search-input"]',
        "link_re":  r"^/(en-[a-z]{2}/[a-z0-9-]+|product/[a-z0-9-]+)$",
    },
    # LapakGaming: close promo modal, switch country (icon -> country-XX -> Save),
    # close promo again, then use the navbar search box. Product pages /en-XX/<slug>.
    # Priced via generic extraction (no lapakgaming.com denom adapter), so best-effort.
    "LapakGaming": {
        "domain":    "lapakgaming.com", "mode": "family", "interactive": True,
        "store":     lambda denom: "https://www.lapakgaming.com/en-my",
        "pre_clicks": [
            '[data-testid="lgmodalpromotionalov-close-button"]',
            '[data-testid="lapakgaming-iconbutton"]',
            lambda d: '[data-testid="lgmodallanguage-buttonitem-country-' + _lapak_cc(d) + '"]',
            'button:has-text("Save")',
            '[data-testid="lgmodalpromotionalov-close-button"]',
        ],
        "open_sel":  '[data-testid="lgheadernavbarmvsearchbox-input"]',
        "input_sel": '[data-testid="lgheadernavbarmvsearchbox-input"]',
        "link_re":   r"^/en-[a-z]{2}/[a-z0-9-]+$",
        "result_sel": "a[href]",
    },
    # UniPin: switch region in the top navbar, then type in the "Search in UniPin"
    # box. Suggestions are list items (no href) -> we click the best match and
    # follow the navigation. Priced via generic extraction (no unipin adapter).
    "Unipin": {
        "domain":    "unipin.com", "mode": "family", "interactive": True,
        "store":     lambda denom: "https://www.unipin.com/en",
        "pre_clicks": [
            'text=Back Home',
            '#top-navbar >> text=Malaysia',
            lambda d: 'a:has-text("' + _country_name(d) + '")',
        ],
        "open_sel":  'input[placeholder*="Search in UniPin" i]',
        "input_sel": 'input[placeholder*="Search in UniPin" i]',
        "result_sel": '[role="listitem"], li',
        "link_re":   r"^/en/",
    },
    # Itemku: open the region picker, accept cookies, pick the continent radio,
    # save, then search. Suggestions are links (/en/...). Priced via generic
    # extraction (no itemku adapter), so best-effort.
    "ItemkuEN": {
        "domain":    "itemku.com", "mode": "family", "interactive": True,
        "store":     lambda denom: "https://www.itemku.com/en/",
        "pre_clicks": [
            'a:has-text("MYR")',                       # open region picker
            'button:has-text("Accept")',               # cookie consent
            lambda d: 'text="' + _itemku_continent(d) + '"',
            'button:has-text("Save Changes")',
        ],
        "open_sel":  'input[placeholder*="Search for Game" i]',
        "input_sel": 'input[placeholder*="Search for Game" i]',
        "result_sel": "a[href]",
        "link_re":   r"^/en/.+",
    },
}
SEARCH_SITES["Moogold"] = SEARCH_SITES["MooGold"]   # catalog uses both spellings

# Generic results-page scraper: collect product links (matching link_re) plus a
# nearby price. The Python side scores these by denomination/name/region.
_SEARCH_RESULTS_JS = r"""
(args) => {
  const linkRe = new RegExp(args.link_re);
  const out = [], seen = new Set();
  for (const a of document.querySelectorAll('a[href]')) {
    const href = a.getAttribute('href') || '';
    if (!linkRe.test(href) || seen.has(href)) continue;
    seen.add(href);
    let text = '', node = a;
    for (let i = 0; i < 5 && node; i++) {
      const t = (node.textContent || '').replace(/\s+/g, ' ').trim();
      if (t.length < 260) text = t;
      node = node.parentElement;
    }
    let price = null; node = a;
    for (let i = 0; i < 6 && node; i++) {
      const m = (node.textContent || '').match(/(?:US\$|\$|€|£)\s?(\d[\d,]*\.\d{2})|(\d[\d,]*\.\d{2})\s*(USD|EUR|GBP)/);
      if (m) { price = parseFloat((m[1] || m[2]).replace(/,/g, '')); break; }
      node = node.parentElement;
    }
    out.push({ url: href, text: text.slice(0, 220), price });
  }
  return out.slice(0, 60);
}
"""


def _search_query(name):
    # Clean the catalog name into a search phrase: drop parenthetical region/notes.
    return re.sub(r"\s+", " ", re.sub(r"\([^)]*\)", " ", name)).strip()


def _coda_region(denom):
    """Codashop is region-specific (/en-XX/). Pick the store from the product's
    region or currency; default to the Malaysian store."""
    r = (denom.get("region") or "").lower()
    cur = (denom.get("currency") or "").upper()
    by_region = {"us": "en-us", "my": "en-my", "sg": "en-sg", "ph": "en-ph",
                 "id": "en-id", "th": "en-th", "vn": "en-vn", "br": "en-br"}
    if r in by_region:
        return by_region[r]
    return {"USD": "en-us", "SGD": "en-sg", "MYR": "en-my"}.get(cur, "en-my")


def _lapak_cc(denom):
    """LapakGaming country code (used in its 'switch country' modal test ids)."""
    r = (denom.get("region") or "").lower()
    cur = (denom.get("currency") or "").upper()
    if r in {"us", "my", "sg", "ph", "id", "th"}:
        return r
    return {"USD": "us", "SGD": "sg", "MYR": "my"}.get(cur, "my")


def _country_name(denom):
    """Full country name for UniPin's region dropdown (links are named by country)."""
    r = (denom.get("region") or "").upper()
    cur = (denom.get("currency") or "").upper()
    names = {"US": "United States", "MY": "Malaysia", "SG": "Singapore",
             "PH": "Philippines", "ID": "Indonesia", "TH": "Thailand"}
    if r in names:
        return names[r]
    return {"USD": "United States", "SGD": "Singapore", "MYR": "Malaysia"}.get(cur, "Malaysia")


def _itemku_continent(denom):
    """Itemku groups its region picker by continent (radio buttons)."""
    r = (denom.get("region") or "").upper()
    cur = (denom.get("currency") or "").upper()
    if r in {"US", "CA", "MX"}:
        return "North America"
    if r in {"MY", "SG", "ID", "TH", "PH", "VN"}:
        return "South East Asia"
    if cur == "USD":
        return "North America"
    if cur in {"EUR", "GBP"}:
        return "Europe"
    return "South East Asia"


async def _open_interactive_search(page, site, store_url, query, denom):
    """For JS-autocomplete sites (no query URL): load the store, run any
    site-specific pre-steps (dismiss modals, switch region), open the search
    widget, type the query, and let suggestions render. Mirrors the recorded
    Playwright codegen flows."""
    await page.goto(store_url, timeout=NAV_TIMEOUT_MS, wait_until="domcontentloaded")
    await page.wait_for_timeout(1200)
    # site-specific pre-steps: each is a CSS selector (str) or a callable(denom)->
    # selector. All best-effort — a missing modal just means nothing to click.
    for step in (site.get("pre_clicks") or []):
        sel = step(denom) if callable(step) else step
        try:
            await page.click(sel, timeout=1500)
            await page.wait_for_timeout(400)
        except Exception:
            continue
    # generic overlay dismiss (cookie / intent iframe) if still in the way
    for sel in ['#wiz-iframe-intent', 'button[aria-label="Close"]',
                '[data-testid="cookie-accept"]', 'text=Accept']:
        try:
            await page.click(sel, timeout=1000)
            break
        except Exception:
            continue
    try:
        await page.click(site["open_sel"], timeout=4000)
    except Exception:
        pass
    try:
        await page.fill(site["input_sel"], query, timeout=4000)
    except Exception:
        return False
    await page.wait_for_timeout(2500)
    return True


# Collect interactive suggestions: each element matching result_sel, with its
# text, an href (if it is/contains/sits under an anchor matching link_re), and its
# index among result_sel matches (so Python can click the nth one if there's no
# href). Used for JS-autocomplete sites whose suggestions may not be plain links.
_INTERACTIVE_JS = r"""
(args) => {
  const linkRe = new RegExp(args.link_re);
  const els = [...document.querySelectorAll(args.result_sel)];
  const out = [];
  els.forEach((el, idx) => {
    const text = (el.textContent || '').replace(/\s+/g, ' ').trim();
    if (!text || text.length > 200) return;
    let href = null;
    const a = el.matches('a[href]') ? el : (el.querySelector('a[href]') || el.closest('a[href]'));
    if (a) { try { const p = new URL(a.href, location.origin).pathname; if (linkRe.test(p)) href = p; } catch (e) {} }
    out.push({ idx, text, href });
  });
  return out.slice(0, 60);
}
"""


def _pick_best(cands, denom, mode):
    """Score search candidates by denomination number, brand words and region.
    "denom" sites require the denomination number in the result; "family" sites
    need only a brand word (the denomination is chosen on the product page)."""
    nums = denom.get("nums") or []
    words = denom.get("words") or []
    region = denom.get("region")
    best, best_score = None, -1
    for c in cands:
        t = c.get("text") or ""
        tl = t.lower()
        s, num_hit = 0, False
        for n in nums:
            if re.search(r"(?<!\d)" + str(n) + r"(?!\d)", t):
                s += 10
                num_hit = True
        if mode == "denom" and nums and not num_hit:
            continue
        for w in words:
            if w in tl:
                s += 1
        if region and re.search(r"\b" + re.escape(region) + r"\b", t, re.I):
            s += 3
        cheaper = (s == best_score and best and c.get("price") and best.get("price")
                   and c["price"] < best["price"])
        if s > best_score or cheaper:
            best, best_score = c, s
    need = 10 if (mode == "denom" and nums) else 1
    return best if (best and best_score >= need) else None


# Kinguin name-search: the /listing page embeds its results (with prices) in
# window._preloadedState.list.productList — each entry has a name carrying the
# denomination + region (e.g. "PlayStation Network Card USD 50 Gift Card US")
# and price.lowestOffer in CENTS. So we can price by name without a product URL,
# reading the embedded JSON instead of scraping cards. (Cloudflare-walled, so it
# still needs the residential/local run.)
_KINGUIN_LIST_JS = r"""
() => {
  const s = window._preloadedState;
  if (!s || !s.list || !s.list.productList) return null;
  const cur = (s.currencies && s.currencies.current && s.currencies.current.code) || 'USD';
  const items = s.list.productList.map(p => {
    const pr = p.price || {};
    const cents = pr.lowestOffer || pr.calculated || null;
    return { name: p.name || p.displayName || '', cents: cents };
  }).filter(x => x.name && typeof x.cents === 'number' && x.cents > 0);
  return { currency: cur, items: items };
}
"""


async def _kinguin_name_search(page, query, denom):
    """Price a Kinguin product by name (no URL): read the listing's embedded
    productList, gate on the denomination total and the region (Global requires a
    Global variant — otherwise N/A, per requirement), take the lowest match."""
    try:
        await page.goto("https://www.kinguin.net/listing?phrase=" + quote_plus(query),
                        timeout=NAV_TIMEOUT_MS, wait_until="domcontentloaded")
        try:
            await page.wait_for_load_state("networkidle", timeout=6000)
        except Exception:
            pass
        await page.wait_for_timeout(1500)
        data = await page.evaluate(_KINGUIN_LIST_JS)
    except Exception:
        data = None
    if not data or not data.get("items"):
        return None
    nums = denom.get("nums") or []
    words = [w.lower() for w in (denom.get("words") or [])]
    region = (denom.get("region") or "").strip()
    # Only restrict by region when the PRODUCT names a specific one. If it's Global
    # (or unspecified) we just take the cheapest matching denomination regardless
    # of which region Kinguin's listing is for.
    region_specific = bool(region) and region.lower() != "global"
    total = max(nums) if nums else None                # base+bonus sum (or the value)
    components = [n for n in nums if n != total]
    def _has(n, name):
        return re.search(r"(?<!\d)" + str(n) + r"(?!\d)", name)
    best_price = None
    for it in data["items"]:
        name = it["name"]; nl = name.lower()
        if region_specific and not re.search(r"\b" + re.escape(region) + r"\b", name, re.I):
            continue
        # Denomination: the listing must represent THIS pack — it carries the TOTAL
        # (e.g. 660) or ALL base+bonus components (600 AND 60). This rejects a
        # smaller pack that only shares one component (e.g. a stray "60 UC" card).
        if nums:
            ok = (total is not None and _has(total, name)) or \
                 (components and all(_has(c, name) for c in components))
            if not ok:
                continue
        if words and not any(w in nl for w in words):
            continue
        price = it["cents"] / 100.0
        if best_price is None or price < best_price:
            best_price = price
    if best_price is None:
        return None
    usd = to_usd(best_price, data.get("currency") or "USD")
    if usd is None or usd <= 0:
        return None
    return {"url": page.url, "price": round(usd, 2), "final": True}


async def resolve_via_search(page, comp, query, denom):
    """Search `comp` for `query`, return {'url':product_url, 'price':card_price}
    for the best denomination/region match, or None if nothing matches."""
    if comp == "Kinguin":
        return await _kinguin_name_search(page, query, denom)
    site = SEARCH_SITES.get(comp)
    if not site:
        return None
    mode = site.get("mode", "denom")
    if site.get("interactive"):
        # JS-autocomplete site: open the widget, type, read suggestions. Suggestions
        # may be plain links (use the href) or list items (click to navigate).
        try:
            store_url = site["store"](denom)
            ok = await _open_interactive_search(page, site, store_url, query, denom)
            if not ok:
                return None
            rsel = site.get("result_sel", "a[href]")
            cands = await page.evaluate(_INTERACTIVE_JS, {"result_sel": rsel, "link_re": site["link_re"]})
        except Exception:
            cands = None
        if not cands:
            return None
        best = _pick_best(cands, denom, mode)
        if not best:
            return None
        if best.get("href"):
            return {"url": urljoin(page.url, best["href"]), "price": None}
        # No href on the suggestion: click it and follow the navigation.
        try:
            await page.locator(site.get("result_sel", "a[href]")).nth(best["idx"]).click(timeout=4000)
            await page.wait_for_load_state("domcontentloaded", timeout=8000)
            await page.wait_for_timeout(1500)
            return {"url": page.url, "price": None}
        except Exception:
            return None
    # URL-based search (marketplace listing pages).
    try:
        await page.goto(site["search"](query), timeout=NAV_TIMEOUT_MS, wait_until="domcontentloaded")
        try:
            await page.wait_for_load_state("networkidle", timeout=6000)
        except Exception:
            pass
        try:
            await page.mouse.wheel(0, 2200)        # nudge lazy-loaded result cards
        except Exception:
            pass
        await page.wait_for_timeout(2000)
        cands = await page.evaluate(_SEARCH_RESULTS_JS, {"link_re": site["link_re"]})
    except Exception:
        cands = None
    if not cands:
        return None
    best = _pick_best(cands, denom, mode)
    if not best:
        return None
    url = best["url"]
    if url.startswith("/"):
        url = urljoin(page.url, url)
    return {"url": url, "price": best.get("price")}


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


# Some catalog URLs have a human note baked into the string with a space, e.g.
# "https://www.seagm.com/battlenet-... (Battle.net Balance - US$50)". A real URL
# never contains a raw space, so anything after the first space is a note. Split
# it off (stripping surrounding parens) so navigation gets a valid URL and the
# note still drives denomination matching.
def split_url_note(u, note):
    if isinstance(u, str) and (" " in u.strip() or "(" in u):
        # URL = leading run with no space and no "(" ; the rest (sans parens) is
        # the note. Handles both "slug (Note)" and "slug(Note text)".
        m = re.match(r"\s*([^\s(]+)\s*\(?\s*(.*?)\)?\s*$", u)
        if m:
            u = m.group(1)
            tail = m.group(2).strip()
            if not note and tail:
                note = tail
    return u, note


# Hook for per-site URL tweaks. NOTE: do not rewrite Eneba's locale — its slugs
# differ per region, so /en-us/ 404s. We keep the given URL and convert currency.
def usd_url(url):
    # SEAGM: use the catalog URL with NO region prefix. Strip any en-xx locale so
    # the slug is region-less; currency is set to USD once per run via the
    # settings form (see seagm_force_usd).
    host = urlparse(url).netloc.replace("www.", "").lower()
    if host.endswith("seagm.com"):
        p = urlparse(url)
        parts = [x for x in p.path.split("/") if x]
        if parts and re.fullmatch(r"[a-z]{2}-[a-z]{2}", parts[0]):
            parts = parts[1:]                # drop any existing locale
        parts = ["en-us"] + parts            # force the en-us (USD) locale
        return p._replace(path="/" + "/".join(parts), query="").geturl()
    return url


# --- fetching ---------------------------------------------------------------
async def fetch_one(context, task, results, report):
    url, comp = task["url"], task["comp"]

    # Search fallback: no stored URL for this competitor -> search by name and
    # resolve the matching product URL first. If nothing matches -> N/A.
    if task.get("search") and not url:
        denom0 = parse_denomination(task["pname"])
        if task.get("region"):
            denom0["region"] = task["region"]          # dashboard-set region drives the search
        q = task.get("query") or task["pname"]
        if comp in API_SEARCH:
            # API-based search (no browser). Returns a product URL (priced below by
            # the adapter) OR a final USD price (recorded directly) OR None.
            try:
                loop = asyncio.get_event_loop()
                result = await loop.run_in_executor(None, API_SEARCH[comp], q, denom0)
            except Exception:
                result = None
            if isinstance(result, (int, float)) and result > 0:
                results.setdefault(task["sheet"], {}).setdefault(task["pname"], {})[comp] = round(float(result), 2)
                report["ok"] += 1
                return
            if not result or not isinstance(result, str):
                results.setdefault(task["sheet"], {}).setdefault(task["pname"], {})[comp] = NA
                report["ok"] += 1
                return
            url = task["url"] = result
        else:
            rpage = await context.new_page()
            try:
                resolved = await resolve_via_search(rpage, comp, q, denom0)
            except Exception:
                resolved = None
            finally:
                try:
                    await rpage.close()
                except Exception:
                    pass
            if not resolved:
                results.setdefault(task["sheet"], {}).setdefault(task["pname"], {})[comp] = NA
                report["ok"] += 1
                return
            # Some searches (e.g. Kinguin) read the price straight from the listing's
            # embedded state — record it directly; there's no product page to scrape.
            if resolved.get("final"):
                sp = resolved.get("price")
                results.setdefault(task["sheet"], {}).setdefault(task["pname"], {})[comp] = (
                    round(float(sp), 2) if isinstance(sp, (int, float)) and sp > 0 else NA)
                report["ok"] += 1
                return
            url = task["url"] = resolved["url"]
            task["_search_price"] = resolved.get("price")

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
            if task.get("region"):
                denom["region"] = task["region"]      # dashboard-set region
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
    # Search fallback: if the product-page adapter found nothing but the search
    # results card showed a price, use that (USD) rather than going N/A.
    sp = task.get("_search_price")
    if isinstance(sp, (int, float)) and sp > 0:
        results.setdefault(task["sheet"], {}).setdefault(task["pname"], {})[comp] = round(float(sp), 2)
        report["ok"] += 1
        return
    # No price detected after all attempts -> record N/A rather than leaving the
    # cell blank (applies to every site). The dashboard auto-replaces N/A with a
    # real price on the next successful run.
    results.setdefault(task["sheet"], {}).setdefault(task["pname"], {})[comp] = NA
    report["failed"] += 1


async def seagm_force_usd(context):
    """Set SEAGM's display currency to USD ONCE for the whole browser context.
    SEAGM stores currency in a cookie; a fresh context defaults to a regional
    currency (e.g. MYR). The settings page /en-us/language_currency has a form
    (POST /en-us/setting) with <select name="currency"> (USD option) and a
    "Save Settings" submit. We set USD + English and submit; the cookie then
    persists so every SEAGM product page in this run prices natively in USD."""
    page = await context.new_page()
    try:
        await page.goto("https://www.seagm.com/language_currency",
                        timeout=NAV_TIMEOUT_MS, wait_until="domcontentloaded")
        try:
            await page.wait_for_load_state("networkidle", timeout=8000)
        except Exception:
            pass
        # dismiss the cookie-consent banner if present (can block the form in headless)
        for sel in ["#CybotCookiebotDialogBodyLevelButtonLevelOptinAllowAll",
                    "#CybotCookiebotDialogBodyButtonAccept", "text=Allow all", "text=Accept All"]:
            try:
                await page.click(sel, timeout=1500)
                break
            except Exception:
                continue
        # set USD + English on the form, then submit via the real button (fallback JS)
        try:
            await page.select_option('select[name="currency"]', "USD", timeout=4000)
        except Exception:
            pass
        try:
            await page.select_option('select[name="language"]', "en", timeout=2000)
        except Exception:
            pass
        submitted = False
        for sel in ['input[type="submit"][value*="Save"]', 'input[type="submit"]',
                    'text=Save Settings']:
            try:
                await page.click(sel, timeout=3000)
                submitted = True
                break
            except Exception:
                continue
        if not submitted:
            await page.evaluate(r"""() => { const c=document.querySelector('select[name="currency"]'); if(c){c.value='USD';c.dispatchEvent(new Event('change',{bubbles:true})); const f=c.closest('form'); if(f) f.submit();} }""")
        try:
            await page.wait_for_load_state("networkidle", timeout=8000)
        except Exception:
            pass
        await page.wait_for_timeout(2000)
        # DEBUG: dump SEAGM cookies so we can pin the currency cookie directly if needed
        try:
            cks = await page.context.cookies("https://www.seagm.com")
            interesting = [f"{c['name']}={c['value']}" for c in cks
                           if re.search(r"curr|lang|locale|region|setting|geo", c["name"], re.I)]
            print(f"  [SEAGM] cookies after submit: {interesting[:10]}", flush=True)
        except Exception:
            pass
        # verify on a product page
        await page.goto("https://www.seagm.com/steam-wallet-card-code-global",
                        timeout=NAV_TIMEOUT_MS, wait_until="domcontentloaded")
        await page.wait_for_timeout(2000)
        try:
            ok = "US$" in (await page.inner_text("body"))
        except Exception:
            ok = False
        print(f"  [SEAGM] currency set to USD: {'ok' if ok else 'UNCONFIRMED'}", flush=True)
    except Exception as e:
        print(f"  [SEAGM] currency setup failed: {type(e).__name__}", flush=True)
    finally:
        await page.close()


async def run(tasks):
    results, report = {}, {"ok": 0, "failed": 0, "errors": []}
    load_fx()  # USD conversion rates for this run
    sem = asyncio.Semaphore(1 if ARGS.debug else CONCURRENCY)

    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=not ARGS.headful)
        context = await browser.new_context(user_agent=USER_AGENT, locale="en-US")

        # One-time: pin SEAGM to USD for the whole context (applies to every
        # SEAGM product), so prices are read in USD with no FX conversion.
        if any("seagm.com" in (t.get("url") or "") for t in tasks):
            await seagm_force_usd(context)

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


def build_tasks(data, only_categories, limit, only_comps=None, skip_comps=None,
                search_comps=None, custom_search=False):
    tasks = []
    searchable = set(SEARCH_SITES) | set(API_SEARCH)

    def comp_ok(comp):
        if comp in SKIP_COMPS:
            return False
        if only_comps and comp not in only_comps:
            return False
        if skip_comps and comp in skip_comps:
            return False
        return True

    for cat, block in data["categories"].items():
        if only_categories and cat not in only_categories:
            continue
        for product in block["products"]:
            present = set(product["urls"].keys())
            is_custom = bool(product.get("custom"))

            # --- DEDICATED custom-product name-search run (run locally) ---------
            # custom_search mode handles ONLY URL-less custom products, searching
            # every marketplace we can. This is heavy (interactive + Cloudflare),
            # so it is opt-in and must NOT run on the 6-hourly cloud job.
            if custom_search:
                if not is_custom:
                    continue
                # 1) brand product-page URLs -> direct URL task (adapter matches denom)
                for comp, info in product["urls"].items():
                    if not comp_ok(comp):
                        continue
                    u = info.get("url") if isinstance(info, dict) else info
                    u, note = split_url_note(u, info.get("note") if isinstance(info, dict) else None)
                    if isinstance(u, str) and u.startswith("http"):
                        tasks.append({"sheet": cat, "pname": product["name"], "comp": comp,
                                      "url": u, "note": note,
                                      "region": product.get("region")})
                # 2) remaining searchable comps without a URL -> name-search
                for comp in searchable:
                    if comp in present or not comp_ok(comp):
                        continue
                    tasks.append({"sheet": cat, "pname": product["name"], "comp": comp,
                                  "url": None, "note": None, "search": True,
                                  "query": _search_query(product["name"]),
                                  "region": product.get("region")})
                continue

            # --- NORMAL run ----------------------------------------------------
            # Price every product that has a stored URL (existing catalogue AND
            # custom brand URLs) via the usual split: the cloud Action handles the
            # datacenter-friendly sites, the local sync handles OG/G2G/G2A/SEAGM.
            # Custom products get URL tasks ONLY — the heavy name-search stays in
            # the dedicated --custom-search run, so this never blows up the runtime.
            for comp, info in product["urls"].items():
                if not comp_ok(comp):
                    continue
                u = info.get("url") if isinstance(info, dict) else info
                u, note = split_url_note(u, info.get("note") if isinstance(info, dict) else None)
                if not (isinstance(u, str) and u.startswith("http")):
                    continue
                tasks.append({"sheet": cat, "pname": product["name"], "comp": comp,
                              "url": u, "note": note,
                              "region": product.get("region") if is_custom else None})
            if is_custom:
                continue   # no name-search fallback for custom products in normal runs
            # Conservative search fallback for existing products missing a URL
            # (only the comps named in --search-comps; default G2A).
            for comp in (search_comps or set()):
                if comp in present or comp not in searchable or not comp_ok(comp):
                    continue
                tasks.append({"sheet": cat, "pname": product["name"], "comp": comp,
                              "url": None, "note": None, "search": True,
                              "query": _search_query(product["name"]),
                              "region": product.get("region")})
    return tasks[:limit] if limit else tasks


def main():
    if not URLS_FILE.exists():
        sys.exit(f"Missing {URLS_FILE} — generate it from the products spreadsheet first.")
    data = json.loads(URLS_FILE.read_text(encoding="utf-8"))

    # Merge user-added products from the dashboard export. These have no URLs, so
    # they're flagged custom=True and priced purely via the name-search fallback
    # (across every competitor we know how to search). Same shape as urls.json.
    if CUSTOM_FILE.exists():
        try:
            custom = json.loads(CUSTOM_FILE.read_text(encoding="utf-8"))
            added = 0
            for cat, blk in (custom.get("categories") or {}).items():
                dst = data["categories"].setdefault(cat, {"products": []})
                existing = {p.get("name") for p in dst["products"]}
                for p in (blk.get("products") or []):
                    name = (p.get("name") or "").strip()
                    if not name or name in existing:
                        continue
                    dst["products"].append({"name": name, "urls": p.get("urls") or {},
                                            "custom": True, "region": p.get("region")})
                    existing.add(name)
                    added += 1
            if added:
                print(f"Merged {added} custom product(s) from {CUSTOM_FILE.name}.", flush=True)
        except Exception as e:
            print(f"  [custom] could not load {CUSTOM_FILE.name}: {type(e).__name__}", flush=True)

    # Brand-level product-page URLs: one URL per brand+competitor, applied to ALL
    # of that brand's denominations. The single-page adapters (OG/SEAGM/MooGold/
    # Eneba/Codashop) then match the right denomination on the page — far more
    # reliable than name-search. Comps without a brand URL still fall back to it.
    if BRAND_URLS_FILE.exists():
        try:
            burls = json.loads(BRAND_URLS_FILE.read_text(encoding="utf-8"))
            applied = 0
            for cat, comp_urls in burls.items():
                blk = data["categories"].get(cat)
                if not blk:
                    continue
                for product in blk["products"]:
                    product.setdefault("urls", {})
                    for comp, u in comp_urls.items():
                        if u and comp not in product["urls"]:
                            product["urls"][comp] = {"url": u}
                            applied += 1
            if applied:
                print(f"Applied {applied} brand URL(s) from {BRAND_URLS_FILE.name}.", flush=True)
        except Exception as e:
            print(f"  [brand_urls] could not load {BRAND_URLS_FILE.name}: {type(e).__name__}", flush=True)

    only = set(c.strip() for c in ARGS.categories.split(",")) if ARGS.categories else None
    only_comps = set(c.strip() for c in ARGS.comps.split(",")) if ARGS.comps else None
    skip_comps = set(c.strip() for c in ARGS.skip_comps.split(",")) if ARGS.skip_comps else None
    search_comps = set(c.strip() for c in ARGS.search_comps.split(",") if c.strip()) if ARGS.search_comps else None
    tasks = build_tasks(data, only, ARGS.limit, only_comps, skip_comps, search_comps,
                        custom_search=ARGS.custom_search)
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
        # Overlay this run's results onto the existing prices. IMPORTANT: never
        # overwrite an existing REAL price with N/A — a site that fails on a given
        # run (e.g. SEAGM/G2A on a datacenter IP, or a transient block) should not
        # wipe the last good value. A real price still overwrites N/A as normal.
        for sheet, prods in results.items():
            for pname, comps in prods.items():
                dst = base.setdefault(sheet, {}).setdefault(pname, {})
                for c, v in comps.items():
                    prev = dst.get(c)
                    if v == NA and isinstance(prev, (int, float)) and prev > 0:
                        continue                      # keep the existing real price
                    dst[c] = v
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

    # Daily snapshot for the dashboard's date picker. `results` is the full merged
    # price set, so today's entry always reflects the latest complete state (the
    # last run of the day wins). Old snapshots are kept (capped at HISTORY_DAYS).
    try:
        today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
        hist = {}
        if HISTORY_FILE.exists():
            try:
                prevh = json.loads(HISTORY_FILE.read_text(encoding="utf-8"))
                hist = prevh.get("history", {}) if isinstance(prevh, dict) else {}
            except Exception:
                hist = {}
        hist[today] = results
        # keep only the most recent HISTORY_DAYS dates
        for d in sorted(hist.keys())[:-HISTORY_DAYS] if len(hist) > HISTORY_DAYS else []:
            del hist[d]
        HISTORY_FILE.write_text(json.dumps(
            {"updated": payload["generated"], "history": hist},
            ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception as e:
        print(f"  [history] snapshot skipped: {type(e).__name__}", flush=True)

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
    ap.add_argument("--search-comps", dest="search_comps", default="G2A",
                    help="competitors to name-search when a product has no stored "
                         "URL (comma-separated; only G2A is verified). Empty to disable.")
    ap.add_argument("--custom-search", dest="custom_search", action="store_true",
                    help="DEDICATED run: name-search ONLY the URL-less custom products "
                         "(from custom_products.json) across every marketplace. Heavy + "
                         "Cloudflare-sensitive — run locally, NOT on the cloud job.")
    ap.add_argument("--skip-comps", dest="skip_comps", default="",
                    help="skip these competitors, e.g. 'OG,G2G' (for the cloud run)")
    ap.add_argument("--merge", action="store_true",
                    help="patch this run's comps into existing prices.json instead of overwriting")
    ap.add_argument("--limit", type=int, default=0, help="cap total fetches (smoke test)")
    ap.add_argument("--headful", action="store_true", help="show the browser window")
    ap.add_argument("--debug", action="store_true", help="save screenshots + findings.json per URL")
    ARGS = ap.parse_args()
    main()
