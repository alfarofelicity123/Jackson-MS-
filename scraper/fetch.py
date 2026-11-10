#!/usr/bin/env python3
"""
Motivated Seller Lead Scraper - Jackson County, MO (Kansas City)

Pipeline
  1. Scrape the Recorder of Deeds portal (Playwright, async) for distressed-
     property document types filed in the last LOOKBACK_DAYS days.
  2. Download the parcel/assessor bulk DBF (requests + BeautifulSoup, with
     __doPostBack support) and build an owner-name lookup.
  3. Enrich records with property + mailing addresses, flag and score them.
  4. Write dashboard/records.json + data/records.json (+ GHL CSV export).

Configuration is via environment variables (all optional):
  CLERK_URL            Clerk / recorder portal URL
  CLERK_FALLBACK_URL   Used if CLERK_URL resolves to a non-portal page (e.g. Google)
  PARCEL_URL           Page or direct file URL for the bulk parcel DBF/ZIP
  PARCEL_LOCAL         Path to a local .dbf/.zip (skips download)
  PARCEL_LINK_HINT     Regex to pick the right download link on the parcel page
  LOOKBACK_DAYS        Default 7
  CLERK_DATE_FMT       Portal date format, default %m/%d/%Y
  CLERK_SEL_*          Override selectors (use '||' to separate alternatives):
                       FROM, TO, DOCTYPE_SELECT, DOCTYPE_INPUT, SEARCH, NEXT, ACCEPT
  NAME_ORDER           FIRST_LAST (default) or LAST_FIRST, used for GHL name split
  HEADLESS             "0" to watch the browser locally
"""
from __future__ import annotations

import argparse
import asyncio
import csv
import hashlib
import io
import json
import logging
import os
import re
import sys
import tempfile
import time
import zipfile
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Optional, Tuple
from urllib.parse import urljoin

import requests
from bs4 import BeautifulSoup

try:  # optional at import time so the module can be unit-tested without them
    from dbfread import DBF
except Exception:  # pragma: no cover
    DBF = None

try:
    from playwright.async_api import async_playwright
except Exception:  # pragma: no cover
    async_playwright = None

# --------------------------------------------------------------------------- #
# Configuration
# --------------------------------------------------------------------------- #
ROOT = Path(__file__).resolve().parent.parent
DASHBOARD_JSON = ROOT / "dashboard" / "records.json"
DATA_JSON = ROOT / "data" / "records.json"
GHL_CSV = ROOT / "data" / "ghl_export.csv"
DEBUG_DIR = ROOT / "data" / "debug"

COUNTY = "Jackson County"
STATE = "MO"
SOURCE = "Jackson County Recorder of Deeds"

CLERK_URL = (os.getenv("CLERK_URL") or "").strip() or "https://aumentumweb.jacksongov.org/RealEstate/SearchEntry.aspx"
CLERK_FALLBACK_URL = (os.getenv("CLERK_FALLBACK_URL") or "").strip() or "https://aumentumweb.jacksongov.org/RealEstate/SearchEntry.aspx"
PARCEL_URL = (os.getenv("PARCEL_URL") or "").strip()  # unknown - see README notes
PARCEL_LOCAL = (os.getenv("PARCEL_LOCAL") or "").strip()
PARCEL_LINK_HINT = os.getenv("PARCEL_LINK_HINT") or r"parcel|owner|cama|dbf|assess"
CLERK_MODE = (os.getenv("CLERK_MODE") or "csv").lower()          # csv (default) | scrape
CLERK_CSV = Path(os.getenv("CLERK_CSV") or (ROOT / "data" / "clerk_import.csv"))
LOOKBACK_DAYS = int(os.getenv("LOOKBACK_DAYS") or "7")
CLERK_DATE_FMT = os.getenv("CLERK_DATE_FMT") or "%m/%d/%Y"
NAME_ORDER = (os.getenv("NAME_ORDER") or "FIRST_LAST").upper()
HEADLESS = os.getenv("HEADLESS", "1") != "0"
MAX_PAGES = int(os.getenv("CLERK_MAX_PAGES") or "30")
RETRIES = 3
UA = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/124.0 Safari/537.36"
)

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)-7s %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger("scraper")

# --------------------------------------------------------------------------- #
# Lead type catalogue
# --------------------------------------------------------------------------- #
# code -> (cat_label, regex matched against the portal's document-type text)
# ORDER MATTERS: first match wins (specific before generic).
LEAD_TYPES: List[Tuple[str, str, str]] = [
    ("RELLP", "Release Lis Pendens", r"release.*lis\s*pendens|rel.*\blp\b|lis\s*pendens.*release"),
    ("LP", "Lis Pendens", r"lis\s*pendens|^\s*lp\s*$"),
    ("NOFC", "Notice of Foreclosure",
     r"notice of (foreclosure|trustee'?s?\s*sale|sale)|foreclos|trustee'?s?\s*sale"),
    ("TAXDEED", "Tax Deed", r"tax\s*deed|collector'?s?\s*deed|sheriff'?s?\s*deed.*tax"),
    ("CCJ", "Certified Judgment", r"certified\s*judg"),
    ("DRJUD", "Domestic Judgment", r"domestic.*judg|divorce.*judg|dissolution.*judg"),
    ("JUD", "Judgment", r"judg"),
    ("LNIRS", "IRS Lien", r"\birs\b|internal revenue"),
    ("LNFED", "Federal Lien", r"federal.*lien|fed(eral)?\s*tax|us\s*(government|treasury)"),
    ("LNCORPTX", "Corp Tax Lien",
     r"corp.*tax.*lien|state\s*tax\s*lien|dept.*revenue|department of revenue"),
    ("LNMECH", "Mechanic Lien", r"mechanic|materialm|contractor'?s?\s*lien"),
    ("LNHOA", "HOA Lien", r"\bhoa\b|homeowner|assoc.*lien|lien.*assoc"),
    ("MEDLN", "Medicaid Lien", r"medicaid|medical assistance|mo\s*healthnet"),
    ("LN", "Lien", r"\blien\b"),
    ("PRO", "Probate Documents",
     r"probate|^\s*prob\s*$|letters\s*(testamentary|of administration)|estate of|small estate"),
    ("NOC", "Notice of Commencement", r"notice of commencement"),
]
LEAD_RX = [(c, l, re.compile(rx, re.I)) for c, l, rx in LEAD_TYPES]
CAT_LABEL = {c: l for c, l, _ in LEAD_TYPES}

JUDGMENT_CATS = {"JUD", "CCJ", "DRJUD"}
TAX_CATS = {"LNCORPTX", "LNIRS", "LNFED", "TAXDEED"}
CORP_RX = re.compile(
    r"\b(LLC|L\.L\.C|INC|INCORPORATED|CORP|CORPORATION|CO|COMPANY|LTD|LP|LLP|"
    r"TRUST|HOLDINGS|PROPERTIES|INVESTMENTS|ENTERPRISES|PARTNERS|PARTNERSHIP|"
    r"BANK|ASSOCIATION|ASSN|REALTY|VENTURES|GROUP|FUND|FUNDERS|CAPITAL|SERVICING|MORTGAGE|"
    r"ANNUITY|INSURANCE|DIVISION|CITY OF|STATE OF|CONDOMINIUM|HOMEOWNERS|NATIONAL|CONSULTING|"
    r"PROTECTION|RENTAL|RENTALS|LIVING|HOMES|DUPLEXES|CITY)\b",
    re.I,
)


ESTATE_RX = re.compile(r"(?<!REAL )\bESTATE$|\bDECEASED\b|\bDESC\b|\bDEC'?D\b|\bESTATE OF\b", re.I)
HOA_RX = re.compile(r"homeowners|home owners|owners ass|association|assn", re.I)
MEDICAID_RX = re.compile(r"health\s*net|medicaid|medical assistance", re.I)
SWAP_CATS = ("LP", "NOFC", "JUD", "CCJ", "DRJUD")


def classify(doc_type_text: str) -> Optional[str]:
    """Map the portal's document-type text to one of our lead codes."""
    t = (doc_type_text or "").strip()
    if not t:
        return None
    for code, _label, rx in LEAD_RX:
        if rx.search(t):
            return code
    return None


# --------------------------------------------------------------------------- #
# Generic helpers
# --------------------------------------------------------------------------- #
def retry_sync(fn: Callable, *args, attempts: int = RETRIES, delay: float = 3.0, **kw):
    last: Optional[Exception] = None
    for i in range(1, attempts + 1):
        try:
            return fn(*args, **kw)
        except Exception as e:  # noqa: BLE001
            last = e
            log.warning("%s failed (attempt %d/%d): %s", getattr(fn, "__name__", "call"), i, attempts, e)
            if i < attempts:
                time.sleep(delay * i)
    raise last  # type: ignore[misc]


async def retry_async(fn: Callable, *args, attempts: int = RETRIES, delay: float = 3.0, **kw):
    last: Optional[Exception] = None
    for i in range(1, attempts + 1):
        try:
            return await fn(*args, **kw)
        except Exception as e:  # noqa: BLE001
            last = e
            log.warning("%s failed (attempt %d/%d): %s", getattr(fn, "__name__", "call"), i, attempts, e)
            if i < attempts:
                await asyncio.sleep(delay * i)
    raise last  # type: ignore[misc]


def clean(s: Any) -> str:
    return re.sub(r"\s+", " ", str(s or "")).strip()


DATE_FORMATS = ("%m/%d/%Y", "%m/%d/%y", "%Y-%m-%d", "%m-%d-%Y", "%b %d, %Y", "%B %d, %Y",
                "%m/%d/%Y %I:%M:%S %p", "%m/%d/%Y %H:%M", "%Y-%m-%dT%H:%M:%S", "%Y%m%d")


def parse_date(s: Any) -> Optional[datetime]:
    t = clean(s)
    if not t:
        return None
    for fmt in DATE_FORMATS:
        try:
            return datetime.strptime(t, fmt)
        except ValueError:
            continue
    m = re.search(r"(\d{1,2})/(\d{1,2})/(\d{2,4})", t)
    if m:
        mo, d, y = int(m.group(1)), int(m.group(2)), int(m.group(3))
        y += 2000 if y < 100 else 0
        try:
            return datetime(y, mo, d)
        except ValueError:
            return None
    return None


def parse_amount(s: Any) -> Optional[float]:
    t = clean(s)
    if not t:
        return None
    m = re.search(r"\$?\s*([\d,]+(?:\.\d{1,2})?)", t)
    if not m:
        return None
    try:
        v = float(m.group(1).replace(",", ""))
        return v if v > 0 else None
    except ValueError:
        return None


def is_corp(name: str) -> bool:
    return bool(CORP_RX.search(name or ""))


# --------------------------------------------------------------------------- #
# Owner-name normalisation and variants
# --------------------------------------------------------------------------- #
_SUFFIX = {"JR", "SR", "II", "III", "IV"}


def norm_name(s: str) -> str:
    s = (s or "").upper().replace("&", " AND ")
    s = re.sub(r"[^A-Z0-9, ]+", " ", s)
    return re.sub(r"\s+", " ", s).strip()


def name_variants(raw: str) -> List[str]:
    """
    Produce lookup keys: "FIRST LAST", "LAST FIRST", "LAST, FIRST" (plus
    first-name-only forms with middle names dropped). Works whichever order
    the source used, because both interpretations are generated.
    """
    n = norm_name(raw)
    if not n:
        return []
    out: List[str] = [n.replace(",", "")]
    if is_corp(n):
        return list(dict.fromkeys(out))

    pairs: List[Tuple[str, List[str]]] = []
    if "," in n:
        left, right = [p.strip() for p in n.split(",", 1)]
        rt = [t for t in right.split() if t not in _SUFFIX]
        if left and rt:
            pairs.append((left.replace(" ", " "), rt))
    else:
        toks = [t for t in n.split() if t not in _SUFFIX]
        if len(toks) >= 2:
            pairs.append((toks[0], toks[1:]))      # LAST FIRST [MID]
            pairs.append((toks[-1], toks[:-1]))    # FIRST [MID] LAST

    for last, rest in pairs:
        for firsts in dict.fromkeys([" ".join(rest)] + ([rest[0]] if len(rest[0]) > 1 else [])):
            out += [f"{firsts} {last}", f"{last} {firsts}", f"{last}, {firsts}"]
    return list(dict.fromkeys(out))


# --------------------------------------------------------------------------- #
# Clerk portal scraping (Playwright async)
# --------------------------------------------------------------------------- #
def _sel(env_key: str, defaults: List[str]) -> List[str]:
    v = os.getenv(env_key)
    return [x.strip() for x in v.split("||") if x.strip()] if v else defaults


SEL_FROM = _sel("CLERK_SEL_FROM", [
    'input[id*="from" i]', 'input[name*="from" i]', 'input[id*="begin" i]',
    'input[id*="start" i]', 'input[name*="start" i]', 'input[placeholder*="from" i]',
])
SEL_TO = _sel("CLERK_SEL_TO", [
    'input[id*="thru" i]', 'input[id*="through" i]', 'input[name*="to" i]:not([name*="total" i])',
    'input[id*="end" i]', 'input[name*="end" i]', 'input[placeholder*="to" i]',
])
SEL_DOCTYPE_SELECT = _sel("CLERK_SEL_DOCTYPE_SELECT", [
    'select[id*="doctype" i]', 'select[name*="doctype" i]', 'select[id*="type" i]',
    'select[name*="type" i]', 'select[id*="instrument" i]',
])
SEL_DOCTYPE_INPUT = _sel("CLERK_SEL_DOCTYPE_INPUT", [
    'input[id*="doctype" i]', 'input[name*="doctype" i]', 'input[id*="instrument" i]',
])
SEL_SEARCH = _sel("CLERK_SEL_SEARCH", [
    'button:has-text("Search")', 'input[type="submit"][value*="Search" i]',
    'input[type="button"][value*="Search" i]', '#searchButton', 'button[type="submit"]',
])
SEL_NEXT = _sel("CLERK_SEL_NEXT", [
    'a:has-text("Next"):not(.disabled)', 'button:has-text("Next"):not([disabled])',
    'a[title*="Next" i]', 'a:has-text("»")', 'li.next:not(.disabled) a',
])
SEL_ACCEPT = _sel("CLERK_SEL_ACCEPT", [
    'button:has-text("Accept")', 'input[value*="Accept" i]', 'a:has-text("I Agree")',
    'button:has-text("I Agree")', 'input[value*="Agree" i]', 'button:has-text("Continue")',
])

HEADER_PATTERNS: List[Tuple[str, re.Pattern]] = [
    ("doc_type", re.compile(r"\btype\b|instrument type|doc.*type", re.I)),
    ("doc_num", re.compile(
        r"(doc(ument)?|instrument|recording|reception|file)\s*(#|no\b|num|number|id)|^number$|^doc$", re.I)),
    ("filed", re.compile(r"record(ed|ing)?\s*date|file[d]?\s*date|date|filed", re.I)),
    ("grantor", re.compile(r"grantor|first\s*party|party\s*1|debtor|defendant|^from$|owner", re.I)),
    ("grantee", re.compile(r"grantee|second\s*party|party\s*2|creditor|plaintiff|^to$", re.I)),
    ("legal", re.compile(r"legal|property\s*desc|subdivision|lot\b|description", re.I)),
    ("amount", re.compile(r"amount|consideration|debt|\$", re.I)),
]


def map_headers(headers: List[str]) -> Dict[str, int]:
    colmap: Dict[str, int] = {}
    for idx, h in enumerate(headers):
        for field, rx in HEADER_PATTERNS:
            if field not in colmap and rx.search(h):
                colmap[field] = idx
                break
    return colmap


def parse_results_html(html: str, base_url: str) -> List[Dict[str, Any]]:
    """Extract raw rows from every recognisable results table on the page."""
    soup = BeautifulSoup(html, "lxml")
    rows: List[Dict[str, Any]] = []
    for table in soup.find_all("table"):
        try:
            trs = table.find_all("tr")
            if len(trs) < 2:
                continue
            header_cells = table.find_all("th") or trs[0].find_all(["td", "th"])
            headers = [clean(c.get_text(" ")) for c in header_cells]
            colmap = map_headers(headers)
            if "doc_type" not in colmap and "doc_num" not in colmap:
                continue
            need = max(colmap.values()) + 1
            for tr in trs:
                tds = tr.find_all("td")
                if len(tds) < need:
                    continue
                try:
                    rec = {f: clean(tds[i].get_text(" ")) for f, i in colmap.items()}
                    a = tr.find("a", href=True)
                    rec["_link"] = urljoin(base_url, a["href"]) if a and not a["href"].startswith(
                        ("javascript", "#")) else ""
                    rec["_link_text"] = clean(a.get_text()) if a else ""
                    rows.append(rec)
                except Exception as e:  # noqa: BLE001
                    log.debug("bad row skipped: %s", e)
        except Exception as e:  # noqa: BLE001
            log.debug("bad table skipped: %s", e)
    return rows


async def _first_visible(page, selectors: List[str]):
    for sel in selectors:
        try:
            loc = page.locator(sel).first
            if await loc.count() and await loc.is_visible():
                return loc
        except Exception:  # noqa: BLE001
            continue
    return None


async def _dump(page, tag: str) -> None:
    try:
        DEBUG_DIR.mkdir(parents=True, exist_ok=True)
        (DEBUG_DIR / f"{tag}.html").write_text(await page.content(), encoding="utf-8")
        await page.screenshot(path=str(DEBUG_DIR / f"{tag}.png"), full_page=True)
    except Exception as e:  # noqa: BLE001
        log.debug("debug dump failed: %s", e)


async def _open_portal(page) -> None:
    await page.goto(CLERK_URL, wait_until="domcontentloaded", timeout=60000)
    await page.wait_for_load_state("networkidle", timeout=30000)
    if "google." in page.url:  # share.google link did not redirect to the portal
        log.warning("CLERK_URL landed on %s; using fallback %s", page.url, CLERK_FALLBACK_URL)
        await page.goto(CLERK_FALLBACK_URL, wait_until="domcontentloaded", timeout=60000)
        await page.wait_for_load_state("networkidle", timeout=30000)
    btn = await _first_visible(page, SEL_ACCEPT)  # disclaimer page
    if btn:
        try:
            await btn.click()
            await page.wait_for_load_state("networkidle", timeout=20000)
        except Exception as e:  # noqa: BLE001
            log.debug("accept click failed: %s", e)
    log.info("Portal ready at %s", page.url)


async def _fill_dates(page, start: datetime, end: datetime) -> bool:
    f = await _first_visible(page, SEL_FROM)
    t = await _first_visible(page, SEL_TO)
    if not f or not t:
        return False
    await f.fill(start.strftime(CLERK_DATE_FMT))
    await t.fill(end.strftime(CLERK_DATE_FMT))
    return True


async def _collect_pages(page) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    seen_sig = set()
    for _ in range(MAX_PAGES):
        html = await page.content()
        rows = parse_results_html(html, page.url)
        sig = hashlib.md5(json.dumps(rows, sort_keys=True).encode()).hexdigest()
        if sig in seen_sig:  # pagination not advancing
            break
        seen_sig.add(sig)
        out.extend(rows)
        nxt = await _first_visible(page, SEL_NEXT)
        if not nxt:
            break
        try:
            await nxt.click()
            await page.wait_for_load_state("networkidle", timeout=20000)
        except Exception:  # noqa: BLE001
            break
    return out


async def _search_once(page, start: datetime, end: datetime, option_label: Optional[str]) -> List[Dict[str, Any]]:
    await _open_portal(page)
    if not await _fill_dates(page, start, end):
        await _dump(page, "no_date_inputs")
        raise RuntimeError("Could not locate date inputs - set CLERK_SEL_FROM / CLERK_SEL_TO")

    if option_label:
        sel = await _first_visible(page, SEL_DOCTYPE_SELECT)
        if sel:
            try:
                await sel.select_option(label=option_label)
            except Exception:  # noqa: BLE001
                await sel.select_option(index=0)
        else:
            inp = await _first_visible(page, SEL_DOCTYPE_INPUT)
            if inp:
                await inp.fill(option_label)

    btn = await _first_visible(page, SEL_SEARCH)
    if not btn:
        await _dump(page, "no_search_btn")
        raise RuntimeError("Could not locate search button - set CLERK_SEL_SEARCH")
    await btn.click()
    await page.wait_for_load_state("networkidle", timeout=45000)
    return await _collect_pages(page)


async def _discover_doctype_options(page) -> List[Tuple[str, str]]:
    """Return [(option_text, lead_code)] for portal doc-type options we care about."""
    await _open_portal(page)
    sel = await _first_visible(page, SEL_DOCTYPE_SELECT)
    if not sel:
        return []
    texts = await sel.locator("option").all_inner_texts()
    found = []
    for t in texts:
        code = classify(t)
        if code:
            found.append((clean(t), code))
    return found


async def scrape_clerk(start: datetime, end: datetime) -> List[Dict[str, Any]]:
    """Return normalised-but-unenriched records from the clerk portal."""
    if async_playwright is None:
        log.error("playwright not installed; skipping clerk scrape")
        return []
    raw_all: List[Tuple[Dict[str, Any], Optional[str]]] = []
    async with async_playwright() as pw:
        browser = await pw.chromium.launch(headless=HEADLESS)
        ctx = await browser.new_context(user_agent=UA, viewport={"width": 1400, "height": 1000})
        page = await ctx.new_page()
        page.set_default_timeout(30000)
        try:
            options = []
            try:
                options = await retry_async(_discover_doctype_options, page)
            except Exception as e:  # noqa: BLE001
                log.error("doc-type discovery failed: %s", e)

            if options:
                log.info("Searching %d matching document types", len(options))
                for label, code in options:
                    try:
                        rows = await retry_async(_search_once, page, start, end, label)
                        log.info("  %-35s -> %d rows", label, len(rows))
                        raw_all += [(r, code) for r in rows]
                    except Exception as e:  # noqa: BLE001
                        log.error("search '%s' failed: %s", label, e)
                        tag = re.sub(r"\W+", "_", label)[:30]
                        await _dump(page, "fail_" + tag)
            else:
                log.info("No doc-type dropdown found; running one broad search")
                try:
                    rows = await retry_async(_search_once, page, start, end, None)
                    raw_all += [(r, None) for r in rows]
                except Exception as e:  # noqa: BLE001
                    log.error("broad search failed: %s", e)
        finally:
            await browser.close()

    records: List[Dict[str, Any]] = []
    for raw, hint in raw_all:
        try:
            rec = normalise_raw(raw, hint)
            if rec:
                records.append(rec)
        except Exception as e:  # noqa: BLE001
            log.debug("record skipped: %s", e)
    return dedupe(records)


def normalise_raw(raw: Dict[str, Any], hint_code: Optional[str]) -> Optional[Dict[str, Any]]:
    doc_type = clean(raw.get("doc_type"))
    code = classify(doc_type) or hint_code
    if not code:
        return None
    filed_dt = parse_date(raw.get("filed"))
    doc_num = clean(raw.get("doc_num")) or clean(raw.get("_link_text"))
    if not doc_num:
        key = f"{doc_type}|{raw.get('grantor')}|{raw.get('filed')}|{raw.get('legal')}"
        doc_num = "X" + hashlib.md5(key.encode()).hexdigest()[:10].upper()
    owner, grantee = clean(raw.get("grantor")), clean(raw.get("grantee"))
    # generic "LIEN": use the lienholder to tell HOA / Medicaid liens apart
    if code == "LN":
        if MEDICAID_RX.search(grantee):
            code = "MEDLN"
        elif HOA_RX.search(grantee):
            code = "LNHOA"
    # lis pendens / foreclosure / judgments: the first party is often the lender or
    # creditor, so when only that name looks institutional the other name is the owner
    if code in SWAP_CATS and is_corp(owner) and grantee and not is_corp(grantee):
        owner, grantee = grantee, owner
    return {
        "doc_num": doc_num,
        "doc_type": doc_type or CAT_LABEL[code],
        "filed": filed_dt.strftime("%Y-%m-%d") if filed_dt else "",
        "cat": code,
        "cat_label": CAT_LABEL[code],
        "owner": owner,
        "grantee": grantee,
        "amount": parse_amount(raw.get("amount")),
        "legal": clean(raw.get("legal")),
        "clerk_url": raw.get("_link") or CLERK_FALLBACK_URL,
    }


def dedupe(records: Iterable[Dict[str, Any]]) -> List[Dict[str, Any]]:
    seen, out = set(), []
    for r in records:
        k = (r["doc_num"], r["cat"])
        if k not in seen:
            seen.add(k)
            out.append(r)
    return out



def load_clerk_csv(path: Path) -> List[Dict[str, Any]]:
    """
    Read a CSV you exported/copied from the recorder search. Column names are
    matched loosely (Document Number, Document Type, Recorded Date, Grantor,
    Grantee, Legal Description, Amount; optional URL/Link column).
    """
    if not path.exists():
        return []
    out: List[Dict[str, Any]] = []
    with path.open("r", newline="", encoding="utf-8-sig", errors="replace") as fh:
        rd = csv.reader(fh)
        try:
            headers = [clean(h) for h in next(rd)]
        except StopIteration:
            return []
        colmap = map_headers([h.lower() for h in headers])
        link_idx = next((i for i, h in enumerate(headers) if re.search(r"url|link", h, re.I)), None)
        if "doc_type" not in colmap:
            log.error("CSV needs a document-type column; headers seen: %s", headers)
            return []
        for row in rd:
            try:
                raw = {f: clean(row[i]) for f, i in colmap.items() if i < len(row)}
                link = clean(row[link_idx]) if link_idx is not None and link_idx < len(row) else ""
                raw["_link"] = link if link.startswith("http") else ""
                rec = normalise_raw(raw, None)
                if rec:
                    out.append(rec)
            except Exception as e:  # noqa: BLE001
                log.debug("csv row skipped: %s", e)
    log.info("Loaded %d lead rows from %s", len(out), path)
    return dedupe(out)

# --------------------------------------------------------------------------- #
# Parcel / property appraiser bulk data (requests + BeautifulSoup + dbfread)
# --------------------------------------------------------------------------- #
PARCEL_COLS = {
    "owner": ["OWNER", "OWN1", "OWNER1", "OWNERNAME", "OWNER_NAME", "NAME"],
    "site_addr": ["SITE_ADDR", "SITEADDR", "SITE_ADDRESS", "SITUS", "PROP_ADDR", "PROPADDR", "ADDRESS"],
    "site_city": ["SITE_CITY", "SITECITY", "PROP_CITY", "PROPCITY"],
    "site_zip": ["SITE_ZIP", "SITEZIP", "PROP_ZIP", "PROPZIP"],
    "mail_addr": ["ADDR_1", "MAILADR1", "MAIL_ADDR", "MAILADDR", "MAIL_ADDR1", "MAILADDR1"],
    "mail_city": ["CITY", "MAILCITY", "MAIL_CITY"],
    "mail_state": ["STATE", "MAILSTATE", "MAIL_STATE"],
    "mail_zip": ["ZIP", "MAILZIP", "MAIL_ZIP", "ZIPCODE", "ZIP_CODE"],
}


def _resolve_cols(fields: List[str]) -> Dict[str, Optional[str]]:
    up = {f.upper(): f for f in fields}
    return {k: next((up[a] for a in aliases if a in up), None) for k, aliases in PARCEL_COLS.items()}


def _hidden_fields(soup: BeautifulSoup) -> Dict[str, str]:
    return {
        i["name"]: i.get("value", "")
        for i in soup.find_all("input", type="hidden")
        if i.get("name")
    }


def _looks_like_file(resp: requests.Response) -> bool:
    ct = resp.headers.get("content-type", "").lower()
    cd = resp.headers.get("content-disposition", "").lower()
    if "attachment" in cd or any(x in ct for x in ("zip", "octet-stream", "dbase", "x-dbf")):
        return True
    return resp.content[:4] == b"PK\x03\x04" or resp.content[:1] in (b"\x03", b"\x83", b"\x8b", b"\xf5")


def _download(session: requests.Session, url: str) -> requests.Response:
    r = session.get(url, timeout=180)
    r.raise_for_status()
    return r


def _find_file_response(session: requests.Session, page_url: str) -> Optional[requests.Response]:
    """Follow a landing page to the actual DBF/ZIP, incl. ASP.NET __doPostBack links."""
    resp = retry_sync(_download, session, page_url)
    if _looks_like_file(resp):
        return resp

    soup = BeautifulSoup(resp.text, "lxml")
    hint = re.compile(PARCEL_LINK_HINT, re.I)

    # 1) plain links to .zip / .dbf
    cands = []
    for a in soup.find_all("a", href=True):
        href = a["href"]
        if re.search(r"\.(zip|dbf)(\?|$)", href, re.I):
            score = 2 if hint.search(a.get_text(" ") + href) else 1
            cands.append((score, urljoin(resp.url, href)))
    if cands:
        cands.sort(reverse=True)
        return retry_sync(_download, session, cands[0][1])

    # 2) __doPostBack('target','arg') links / buttons
    pb_rx = re.compile(r"__doPostBack\(\s*'([^']*)'\s*,\s*'([^']*)'\s*\)")
    targets = []
    for el in soup.find_all(["a", "input", "button"]):
        blob = (el.get("href") or "") + " " + (el.get("onclick") or "")
        m = pb_rx.search(blob)
        if m:
            label = el.get_text(" ") or el.get("value", "") or ""
            targets.append((2 if hint.search(label + m.group(1)) else 1, m.group(1), m.group(2), clean(label)))
    targets.sort(reverse=True)

    for _score, target, arg, label in targets[:6]:
        try:
            form = soup.find("form")
            action = urljoin(resp.url, form.get("action")) if form and form.get("action") else resp.url
            data = _hidden_fields(soup)
            data.update({"__EVENTTARGET": target, "__EVENTARGUMENT": arg})
            log.info("POST __doPostBack target=%s (%s)", target, label[:40])

            def _post():
                r = session.post(action, data=data, timeout=240, headers={"Referer": resp.url})
                r.raise_for_status()
                return r

            pr = retry_sync(_post)
            if _looks_like_file(pr):
                return pr
            # response may be a page that now exposes the real link
            soup2 = BeautifulSoup(pr.text, "lxml")
            for a in soup2.find_all("a", href=True):
                if re.search(r"\.(zip|dbf)(\?|$)", a["href"], re.I):
                    return retry_sync(_download, session, urljoin(pr.url, a["href"]))
        except Exception as e:  # noqa: BLE001
            log.warning("postback %s failed: %s", target, e)
    return None


def _extract_dbf(blob: bytes, workdir: Path) -> Optional[Path]:
    if blob[:4] == b"PK\x03\x04":
        with zipfile.ZipFile(io.BytesIO(blob)) as z:
            dbfs = [n for n in z.namelist() if n.lower().endswith(".dbf")]
            if not dbfs:
                return None
            dbfs.sort(key=lambda n: (("parcel" not in n.lower()), -z.getinfo(n).file_size))
            z.extractall(workdir)  # also extracts .dbt/.fpt memo files if present
            return workdir / dbfs[0]
    p = workdir / "parcels.dbf"
    p.write_bytes(blob)
    return p


def load_parcels() -> Optional[Path]:
    """Return path to a local DBF file, or None if unavailable."""
    workdir = Path(tempfile.mkdtemp(prefix="parcels_"))
    try:
        if PARCEL_LOCAL and Path(PARCEL_LOCAL).exists():
            blob = Path(PARCEL_LOCAL).read_bytes()
            return _extract_dbf(blob, workdir)
        if not PARCEL_URL:
            log.warning("PARCEL_URL not set - skipping parcel enrichment. "
                        "Set it (repo variable) once a bulk DBF source is found.")
            return None
        session = requests.Session()
        session.headers.update({"User-Agent": UA})
        resp = _find_file_response(session, PARCEL_URL)
        if resp is None:
            log.error("No downloadable parcel file found at %s", PARCEL_URL)
            return None
        return _extract_dbf(resp.content, workdir)
    except Exception as e:  # noqa: BLE001
        log.error("Parcel download failed: %s", e)
        return None


def build_owner_lookup(dbf_path: Path) -> Dict[str, Dict[str, str]]:
    if DBF is None:
        log.error("dbfread not installed")
        return {}
    lookup: Dict[str, Dict[str, str]] = {}
    table = DBF(str(dbf_path), encoding="latin-1", ignore_missing_memofile=True,
                char_decode_errors="ignore", load=False)
    cols = _resolve_cols(list(table.field_names))
    log.info("Parcel columns resolved: %s", cols)
    if not cols["owner"]:
        log.error("No owner column in parcel file; fields=%s", table.field_names)
        return {}
    n = 0
    for row in table:
        try:
            owner = clean(row.get(cols["owner"]))
            if not owner:
                continue
            info = {k: clean(row.get(c)) if c else "" for k, c in cols.items()}
            for v in name_variants(owner):
                lookup.setdefault(v, info)
            n += 1
        except Exception:  # noqa: BLE001
            continue
    log.info("Parcel lookup: %d parcels, %d name keys", n, len(lookup))
    return lookup


def lookup_owner(lookup: Dict[str, Dict[str, str]], *names: str) -> Optional[Dict[str, str]]:
    for nm in names:
        for v in name_variants(nm):
            hit = lookup.get(v)
            if hit:
                return hit
    return None


def enrich(records: List[Dict[str, Any]], lookup: Dict[str, Dict[str, str]]) -> None:
    for r in records:
        try:
            hit = lookup_owner(lookup, r["owner"], r["grantee"]) if lookup else None
            r.update({
                "prop_address": hit["site_addr"] if hit else "",
                "prop_city": (hit["site_city"] if hit else "") or "",
                "prop_state": STATE if hit and hit["site_addr"] else "",
                "prop_zip": hit["site_zip"] if hit else "",
                "mail_address": hit["mail_addr"] if hit else "",
                "mail_city": hit["mail_city"] if hit else "",
                "mail_state": hit["mail_state"] if hit else "",
                "mail_zip": hit["mail_zip"] if hit else "",
            })
        except Exception as e:  # noqa: BLE001
            log.debug("enrich failed for %s: %s", r.get("doc_num"), e)


# --------------------------------------------------------------------------- #
# Flags + scoring
# --------------------------------------------------------------------------- #
def compute_flags(r: Dict[str, Any], new_cutoff: datetime) -> List[str]:
    flags: List[str] = []
    c = r["cat"]
    if c == "LP":
        flags.append("Lis pendens")
    if c == "NOFC":
        flags.append("Pre-foreclosure")
    if c in JUDGMENT_CATS:
        flags.append("Judgment lien")
    if c in TAX_CATS:
        flags.append("Tax lien")
    if c == "LNMECH":
        flags.append("Mechanic lien")
    if c == "PRO" or ESTATE_RX.search(r.get("owner", "")) or ESTATE_RX.search(r.get("grantee", "")):
        flags.append("Probate / estate")
    if is_corp(r.get("owner", "")):
        flags.append("LLC / corp owner")
    d = parse_date(r.get("filed"))
    if d and d >= new_cutoff:
        flags.append("New this week")
    return flags


def score_all(records: List[Dict[str, Any]], new_cutoff: datetime) -> None:
    # owners holding both an LP and a foreclosure notice anywhere in the batch
    by_owner: Dict[str, set] = {}
    for r in records:
        k = norm_name(r.get("owner", ""))
        if k:
            by_owner.setdefault(k, set()).add(r["cat"])

    for r in records:
        try:
            r["flags"] = compute_flags(r, new_cutoff)
            s = 30 + 10 * len(r["flags"])
            cats = by_owner.get(norm_name(r.get("owner", "")), {r["cat"]})
            if "LP" in cats and "NOFC" in cats:
                s += 20
            amt = r.get("amount") or 0
            if amt > 100_000:
                s += 15
            elif amt > 50_000:
                s += 10
            if "New this week" in r["flags"]:
                s += 5
            if r.get("prop_address") or r.get("mail_address"):
                s += 5
            r["score"] = max(0, min(100, int(s)))
        except Exception as e:  # noqa: BLE001
            log.debug("score failed for %s: %s", r.get("doc_num"), e)
            r["flags"], r["score"] = r.get("flags", []), 30


# --------------------------------------------------------------------------- #
# Output
# --------------------------------------------------------------------------- #
RECORD_KEYS = [
    "doc_num", "doc_type", "filed", "cat", "cat_label", "owner", "grantee", "amount", "legal",
    "prop_address", "prop_city", "prop_state", "prop_zip",
    "mail_address", "mail_city", "mail_state", "mail_zip",
    "clerk_url", "flags", "score",
]


def finalise(records: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    out = []
    for r in records:
        out.append({k: r.get(k, [] if k == "flags" else ("" if k != "amount" else None))
                    for k in RECORD_KEYS})
    return out


def write_outputs(records: List[Dict[str, Any]], start: datetime, end: datetime) -> Dict[str, Any]:
    payload = {
        "fetched_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "source": f"{SOURCE} - {COUNTY}, {STATE}",
        "date_range": {"start": start.strftime("%Y-%m-%d"), "end": end.strftime("%Y-%m-%d")},
        "total": len(records),
        "with_address": sum(1 for r in records if r.get("prop_address") or r.get("mail_address")),
        "records": records,
    }
    for path in (DASHBOARD_JSON, DATA_JSON):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
        log.info("Wrote %s", path)
    return payload


def split_name(owner: str) -> Tuple[str, str]:
    o = clean(owner)
    if not o:
        return "", ""
    if is_corp(o):
        return "", o
    if "," in o:
        last, first = [p.strip() for p in o.split(",", 1)]
        return first.title(), last.title()
    toks = o.split()
    if len(toks) == 1:
        return "", toks[0].title()
    if NAME_ORDER == "LAST_FIRST":
        return " ".join(toks[1:]).title(), toks[0].title()
    return " ".join(toks[:-1]).title(), toks[-1].title()


GHL_COLUMNS = [
    "First Name", "Last Name", "Mailing Address", "Mailing City", "Mailing State", "Mailing Zip",
    "Property Address", "Property City", "Property State", "Property Zip", "Lead Type",
    "Document Type", "Date Filed", "Document Number", "Amount/Debt Owed", "Seller Score",
    "Motivated Seller Flags", "Source", "Public Records URL",
]


def export_ghl_csv(records: List[Dict[str, Any]], path: Path = GHL_CSV) -> Path:
    """Write a GoHighLevel-importable CSV."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=GHL_COLUMNS)
        w.writeheader()
        for r in records:
            try:
                first, last = split_name(r.get("owner", ""))
                w.writerow({
                    "First Name": first, "Last Name": last,
                    "Mailing Address": r.get("mail_address", ""), "Mailing City": r.get("mail_city", ""),
                    "Mailing State": r.get("mail_state", ""), "Mailing Zip": r.get("mail_zip", ""),
                    "Property Address": r.get("prop_address", ""), "Property City": r.get("prop_city", ""),
                    "Property State": r.get("prop_state", ""), "Property Zip": r.get("prop_zip", ""),
                    "Lead Type": r.get("cat_label", ""), "Document Type": r.get("doc_type", ""),
                    "Date Filed": r.get("filed", ""), "Document Number": r.get("doc_num", ""),
                    "Amount/Debt Owed": f"{r['amount']:.2f}" if r.get("amount") else "",
                    "Seller Score": r.get("score", ""),
                    "Motivated Seller Flags": "; ".join(r.get("flags", [])),
                    "Source": SOURCE, "Public Records URL": r.get("clerk_url", ""),
                })
            except Exception as e:  # noqa: BLE001
                log.debug("ghl row skipped: %s", e)
    log.info("Wrote %s", path)
    return path


# --------------------------------------------------------------------------- #
# Main
# --------------------------------------------------------------------------- #
async def run(days: int) -> Dict[str, Any]:
    end = datetime.now()
    start = end - timedelta(days=days)
    new_cutoff = end - timedelta(days=7)
    log.info("Jackson County MO scrape: %s -> %s", start.date(), end.date())

    records: List[Dict[str, Any]] = []
    try:
        if CLERK_MODE == "scrape":
            records = await scrape_clerk(start, end)
        else:
            records = load_clerk_csv(CLERK_CSV)
            if not records:
                log.warning("No leads: put your exported CSV at %s (see README note)", CLERK_CSV)
    except Exception as e:  # noqa: BLE001
        log.error("Clerk step crashed: %s", e)

    # drop anything outside the lookback window (portal filters are sometimes loose)
    keep = []
    for r in records:
        d = parse_date(r.get("filed"))
        if d is None or d.date() >= start.date():
            keep.append(r)
    records = keep
    log.info("Clerk records: %d", len(records))

    lookup: Dict[str, Dict[str, str]] = {}
    try:
        dbf = load_parcels()
        if dbf:
            lookup = build_owner_lookup(dbf)
    except Exception as e:  # noqa: BLE001
        log.error("Parcel step failed: %s", e)

    enrich(records, lookup)
    score_all(records, new_cutoff)
    records = finalise(records)
    records.sort(key=lambda r: r["score"], reverse=True)

    payload = write_outputs(records, start, end)
    try:
        export_ghl_csv(records)
    except Exception as e:  # noqa: BLE001
        log.error("GHL export failed: %s", e)
    log.info("Done: %d records (%d with address)", payload["total"], payload["with_address"])
    return payload


def main() -> int:
    ap = argparse.ArgumentParser(description="Jackson County MO motivated seller scraper")
    ap.add_argument("--days", type=int, default=LOOKBACK_DAYS)
    args = ap.parse_args()
    try:
        asyncio.run(run(args.days))
    except Exception as e:  # noqa: BLE001  - never fail the workflow without output
        log.exception("Fatal: %s", e)
        now = datetime.now()
        write_outputs([], now - timedelta(days=args.days), now)
    return 0


if __name__ == "__main__":
    sys.exit(main())
