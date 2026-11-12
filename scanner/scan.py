"""Career Watch feed builder.

Scans UAE companies' own careers pages on a daily rotation and writes
career_jobs.json at the repo root.

Flow per run:
  1. Discovery: for companies not yet checked, find the careers page
     (homepage link, common paths, careers./jobs. subdomains) and detect the
     applicant-tracking system (Greenhouse, Lever, Workable, ...).
  2. Scan: read the open jobs (public ATS JSON APIs where possible, otherwise
     the careers page HTML / JSON-LD), keep business/data-type roles in the
     UAE, and track first_seen / last_seen in state/jobs_db.json.
  3. Write career_jobs.json for the Career Watch scheduled task.

Settings come from environment variables (see the workflow file).
"""
import csv
import html as htmlmod
import json
import os
import re
import threading
import time
import traceback
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from urllib.parse import urljoin, urlparse, urldefrag
from urllib import robotparser

import requests
from bs4 import BeautifulSoup

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
COMPANIES_CSV = os.path.join(ROOT, "companies.csv")
SEED_CSV = os.path.join(ROOT, "companies_seed.csv")
STATE_DIR = os.path.join(ROOT, "state")
COMPANY_STATE = os.path.join(STATE_DIR, "companies_state.json")
JOBS_DB = os.path.join(STATE_DIR, "jobs_db.json")
OUT_FILE = os.path.join(ROOT, "career_jobs.json")

MAX_MINUTES = float(os.environ.get("MAX_MINUTES", "200"))
DISCOVERY_PER_RUN = int(os.environ.get("DISCOVERY_PER_RUN", "900"))
SCAN_PER_RUN = int(os.environ.get("SCAN_PER_RUN", "1500"))
WORKERS = int(os.environ.get("WORKERS", "24"))
FEED_DAYS = int(os.environ.get("FEED_DAYS", "21"))
DESC_FETCH_LIMIT = int(os.environ.get("DESC_FETCH_LIMIT", "600"))
MAX_FEED_JOBS = int(os.environ.get("MAX_FEED_JOBS", "1500"))
REDISCOVER_NONE_DAYS = 45
REDISCOVER_ERROR_DAYS = 10

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0 Safari/537.36 career-feed/1.0")
HEADERS = {"User-Agent": UA, "Accept-Language": "en-US,en;q=0.8",
           "Accept": "text/html,application/xhtml+xml,application/json;q=0.9,*/*;q=0.8"}
TIMEOUT = (8, 20)

NOW = datetime.now(timezone.utc)
NOW_ISO = NOW.strftime("%Y-%m-%dT%H:%M:%SZ")
START = time.time()

_local = threading.local()


def session():
    s = getattr(_local, "s", None)
    if s is None:
        s = requests.Session()
        s.headers.update(HEADERS)
        _local.s = s
    return s


def time_left():
    return MAX_MINUTES * 60 - (time.time() - START)


def get(url, **kw):
    kw.setdefault("timeout", TIMEOUT)
    kw.setdefault("allow_redirects", True)
    return session().get(url, **kw)


def post(url, **kw):
    kw.setdefault("timeout", TIMEOUT)
    return session().post(url, **kw)


# --------------------------------------------------------------------------
# robots.txt (only for plain HTML careers pages; ATS JSON APIs are public)
# --------------------------------------------------------------------------
_robots = {}
_robots_lock = threading.Lock()


def allowed(url):
    p = urlparse(url)
    base = f"{p.scheme}://{p.netloc}"
    with _robots_lock:
        rp = _robots.get(base)
    if rp is None:
        rp = robotparser.RobotFileParser()
        try:
            r = get(base + "/robots.txt", timeout=(5, 10))
            if r.status_code == 200 and len(r.text) < 500_000:
                rp.parse(r.text.splitlines())
            else:
                rp.parse([])
        except Exception:  # noqa: BLE001
            rp.parse([])
        with _robots_lock:
            _robots[base] = rp
    try:
        return rp.can_fetch(UA, url)
    except Exception:  # noqa: BLE001
        return True


# --------------------------------------------------------------------------
# Text helpers and filters
# --------------------------------------------------------------------------
WS = re.compile(r"\s+")


def clean(t):
    return WS.sub(" ", t or "").strip()


def html_to_text(h, limit=3000):
    if not h:
        return ""
    h = htmlmod.unescape(h) if "&lt;" in h else h
    soup = BeautifulSoup(h, "lxml")
    for t in soup(["script", "style", "noscript"]):
        t.decompose()
    return clean(soup.get_text(" "))[:limit]


UAE_RE = re.compile(
    r"\b(uae|u\.a\.e\.?|united arab emirates|dubai|abu dhabi|abudhabi|sharjah|ajman|"
    r"ras al[- ]?khaimah|\brak\b|fujairah|umm al[- ]?quwain|al ain|jebel ali|difc|adgm|"
    r"jlt|masdar|musaffah|mussafah|ruwais|khalifa city|dubai south|emirates)\b", re.I)
FOREIGN_RE = re.compile(
    r"\b(saudi|ksa|riyadh|jeddah|dammam|khobar|qatar|doha|bahrain|manama|kuwait|oman|muscat|"
    r"egypt|cairo|jordan|amman|lebanon|beirut|morocco|casablanca|turkey|istanbul|pakistan|"
    r"karachi|lahore|india|bangalore|bengaluru|mumbai|delhi|gurgaon|gurugram|hyderabad|pune|"
    r"chennai|kochi|london|united kingdom|\buk\b|england|ireland|dublin|germany|berlin|munich|"
    r"france|paris|spain|madrid|netherlands|amsterdam|usa|united states|new york|"
    r"singapore|hong kong|china|shanghai|japan|tokyo|australia|sydney|canada|toronto|"
    r"south africa|nigeria|kenya|nairobi|philippines|manila|sri lanka|colombo)\b", re.I)


def location_ok(loc):
    loc = clean(loc)
    if not loc:
        return True
    if UAE_RE.search(loc):
        return True
    if FOREIGN_RE.search(loc):
        return False
    # Unknown wording ("Remote", "Head Office", "Multiple") -> keep, task decides
    return True


SENIOR_RE = re.compile(
    r"\b(director|head of|head,|head -|vp|vice president|chief|ceo|cfo|cto|coo|cio|cdo|"
    r"principal|partner|general manager|svp|evp|managing director)\b", re.I)
OFF_DOMAIN_RE = re.compile(
    r"\b(nurse|nursing|physician|doctor|surgeon|pharmac\w*|dentist|dental|therapist|"
    r"radiograph\w*|midwife|teacher|lecturer|professor|tutor|chef|cook|waiter|waitress|"
    r"housekeep\w*|steward\w*|driver|mechanic|electrician|plumber|welder|security guard|"
    r"cyber|soc analyst|penetration|malware|lab analyst|laboratory|chemist|cashier|barista|"
    r"cabin crew|pilot|lifeguard|beautician|stylist|sales associate|telesales)\b", re.I)
TIER1_RE = re.compile(
    r"(business analyst|data analyst|bi analyst|business intelligence|power ?bi|\bmis\b|"
    r"reporting (analyst|specialist|executive|officer|lead|associate)|insights? analyst|"
    r"analytics|odoo|\berp\b|\bcrm\b|business systems?|systems analyst|business process|"
    r"process (analyst|improvement|excellence)|operations? excellence|operational excellence|"
    r"automation (analyst|specialist|engineer|lead|executive|consultant)|\brpa\b|"
    r"\bai (specialist|analyst|automation|consultant|solutions)|revenue (analyst|management|manager)|"
    r"pricing analyst|commercial analyst|strategy (analyst|associate|executive|specialist|consultant)|"
    r"operations analyst|performance analyst|planning analyst|fp&a|kpi|"
    r"data (specialist|executive|officer|coordinator|associate|engineer|management)|"
    r"product analyst|\banalyst\b)", re.I)
TIER2_RE = re.compile(
    r"(\bdata\b|digital transformation|transformation|implementation|functional consultant|"
    r"\bpmo\b|project coordinator|operations (executive|coordinator|specialist|associate|officer)|"
    r"planning (executive|specialist|coordinator|officer)|sales operations|revenue|"
    r"commercial (executive|coordinator)|insights|reporting|dashboard|"
    r"systems (specialist|administrator|executive|officer)|business (consultant|associate|excellence)|"
    r"\bprocess\b|strategy|automation|\bai\b|artificial intelligence|machine learning|"
    r"product (owner|specialist|executive)|mis executive|information systems)", re.I)


def tier_for(title):
    t = clean(title)
    if not t or len(t) > 160:
        return 0
    if SENIOR_RE.search(t) or OFF_DOMAIN_RE.search(t):
        return 0
    if TIER1_RE.search(t):
        return 1
    if TIER2_RE.search(t):
        return 2
    return 0


# --------------------------------------------------------------------------
# ATS detection
# --------------------------------------------------------------------------
ATS_PATTERNS = [
    ("greenhouse", re.compile(r"greenhouse\.io/embed/job_board(?:/js)?\?for=([A-Za-z0-9_-]+)", re.I)),
    ("greenhouse", re.compile(r"(?:boards|job-boards)(?:\.eu)?\.greenhouse\.io/([A-Za-z0-9_-]+)", re.I)),
    ("lever", re.compile(r"jobs\.(?:eu\.)?lever\.co/([A-Za-z0-9_.-]+)", re.I)),
    ("workable", re.compile(r"apply\.workable\.com/(?:api/v\d/widget/accounts/)?([A-Za-z0-9_-]+)", re.I)),
    ("workable", re.compile(r"https?://([a-z0-9-]+)\.workable\.com", re.I)),
    ("smartrecruiters", re.compile(r"(?:jobs|careers)\.smartrecruiters\.com/([A-Za-z0-9_-]+)", re.I)),
    ("ashby", re.compile(r"jobs\.ashbyhq\.com/([A-Za-z0-9_.%-]+)", re.I)),
    ("recruitee", re.compile(r"https?://([a-z0-9-]+)\.recruitee\.com", re.I)),
    ("teamtailor", re.compile(r"https?://([a-z0-9-]+)\.teamtailor\.com", re.I)),
    ("workday", re.compile(r"https?://([a-z0-9-]+)\.(wd\d+)\.myworkdayjobs\.com/(?:[a-z]{2}-[A-Z]{2}/)?([A-Za-z0-9_-]+)")),
    ("personio", re.compile(r"https?://([a-z0-9-]+)\.jobs\.personio\.(?:de|com)", re.I)),
    ("breezy", re.compile(r"https?://([a-z0-9-]+)\.breezy\.hr", re.I)),
    ("bamboohr", re.compile(r"https?://([a-z0-9-]+)\.bamboohr\.com", re.I)),
]
BAD_SLUGS = {"embed", "api", "j", "www", "app", "apply", "jobs", "careers", "static", "assets",
             "wday", "cdn", "help", "support", "login", "v1", "js", "boards", "job-boards"}
UNSUPPORTED_RE = re.compile(
    r"(oraclecloud\.com/hcmUI|successfactors\.(?:com|eu)|career\d*\.successfactors|jobs\.sap\.com|"
    r"taleo\.net|icims\.com|avature\.net|csod\.com|ultipro\.com|dayforcehcm\.com|"
    r"myworkdaysite\.com|peopleclick|brassring\.com|kenexa)", re.I)


def detect_ats(text):
    for name, rx in ATS_PATTERNS:
        for m in rx.finditer(text or ""):
            if name == "workday":
                tenant, wd, site = m.group(1), m.group(2), m.group(3)
                if site.lower() in BAD_SLUGS:
                    continue
                return name, f"{tenant}|{wd}|{site}"
            slug = m.group(1)
            if slug.lower() in BAD_SLUGS:
                continue
            return name, slug
    return None, None


def detect_unsupported(text):
    m = UNSUPPORTED_RE.search(text or "")
    return m.group(1).split(".")[0].lower() if m else None


# --------------------------------------------------------------------------
# ATS fetchers -> list of {title, location, url, description}
# --------------------------------------------------------------------------
def f_greenhouse(slug):
    for host in ("boards-api.greenhouse.io", "boards-api.eu.greenhouse.io"):
        r = get(f"https://{host}/v1/boards/{slug}/jobs", params={"content": "true"})
        if r.status_code == 200:
            return [{"title": j.get("title", ""),
                     "location": (j.get("location") or {}).get("name", ""),
                     "url": j.get("absolute_url", ""),
                     "description": html_to_text(j.get("content", ""))}
                    for j in r.json().get("jobs", [])]
    r.raise_for_status()
    return []


def f_lever(slug):
    for host in ("api.lever.co", "api.eu.lever.co"):
        r = get(f"https://{host}/v0/postings/{slug}", params={"mode": "json"})
        if r.status_code == 200:
            out = []
            for j in r.json():
                desc = j.get("descriptionPlain", "") or ""
                for lst in j.get("lists", []) or []:
                    desc += " " + lst.get("text", "") + ": " + html_to_text(lst.get("content", ""))
                cats = j.get("categories") or {}
                loc = cats.get("location", "") or ", ".join(cats.get("allLocations", []) or [])
                out.append({"title": j.get("text", ""), "location": loc,
                            "url": j.get("hostedUrl", ""), "description": clean(desc)[:3000]})
            return out
    r.raise_for_status()
    return []


def f_workable(slug):
    r = get(f"https://apply.workable.com/api/v1/widget/accounts/{slug}", params={"details": "true"})
    r.raise_for_status()
    out = []
    for j in r.json().get("jobs", []):
        loc = ", ".join(x for x in [j.get("city"), j.get("state"), j.get("country")] if x)
        if not loc and j.get("locations"):
            l0 = j["locations"][0]
            loc = ", ".join(x for x in [l0.get("city"), l0.get("country")] if x)
        out.append({"title": j.get("title", ""), "location": loc,
                    "url": j.get("url") or j.get("shortlink") or
                    f"https://apply.workable.com/{slug}/j/{j.get('shortcode', '')}/",
                    "description": html_to_text(j.get("description", ""))})
    return out


def f_smartrecruiters(slug):
    out, offset = [], 0
    while offset < 1000:
        r = get(f"https://api.smartrecruiters.com/v1/companies/{slug}/postings",
                params={"limit": 100, "offset": offset})
        r.raise_for_status()
        d = r.json()
        for j in d.get("content", []):
            loc = j.get("location") or {}
            out.append({"title": j.get("name", ""),
                        "location": ", ".join(x for x in [loc.get("city"), loc.get("country")] if x),
                        "url": f"https://jobs.smartrecruiters.com/{slug}/{j.get('id')}",
                        "description": "", "_sr": (slug, j.get("id"))})
        offset += 100
        if offset >= d.get("totalFound", 0):
            break
    return out


def d_smartrecruiters(slug, jid):
    r = get(f"https://api.smartrecruiters.com/v1/companies/{slug}/postings/{jid}")
    r.raise_for_status()
    secs = (r.json().get("jobAd") or {}).get("sections") or {}
    parts = [html_to_text((secs.get(k) or {}).get("text", ""), 2000)
             for k in ("jobDescription", "qualifications", "additionalInformation")]
    return clean(" ".join(parts))[:3000]


def f_ashby(slug):
    r = get(f"https://api.ashbyhq.com/posting-api/job-board/{slug}")
    r.raise_for_status()
    return [{"title": j.get("title", ""), "location": j.get("location", ""),
             "url": j.get("jobUrl", ""),
             "description": clean(j.get("descriptionPlain", ""))[:3000]}
            for j in r.json().get("jobs", [])]


def f_recruitee(slug):
    r = get(f"https://{slug}.recruitee.com/api/offers/")
    r.raise_for_status()
    return [{"title": j.get("title", ""),
             "location": j.get("location", "") or ", ".join(
                 x for x in [j.get("city"), j.get("country")] if x),
             "url": j.get("careers_url", ""),
             "description": html_to_text((j.get("description") or "") + " " + (j.get("requirements") or ""))}
            for j in r.json().get("offers", [])]


def f_teamtailor(slug):
    r = get(f"https://{slug}.teamtailor.com/jobs.rss")
    r.raise_for_status()
    soup = BeautifulSoup(r.content, "xml")
    out = []
    for it in soup.find_all("item"):
        loc = ""
        for tag in ("tt:location", "location", "tt:city"):
            el = it.find(tag)
            if el:
                loc = clean(el.get_text(" "))
                break
        out.append({"title": clean(it.title.get_text() if it.title else ""), "location": loc,
                    "url": clean(it.link.get_text() if it.link else ""),
                    "description": html_to_text(it.description.get_text() if it.description else "")})
    return out


def f_workday(key):
    tenant, wd, site = key.split("|")
    base = f"https://{tenant}.{wd}.myworkdayjobs.com"
    api = f"{base}/wday/cxs/{tenant}/{site}/jobs"
    out, offset, total = [], 0, None
    while offset < 400:
        r = post(api, json={"appliedFacets": {}, "limit": 20, "offset": offset, "searchText": ""},
                 headers={"Content-Type": "application/json", "Accept": "application/json"})
        r.raise_for_status()
        d = r.json()
        if total is None:
            total = d.get("total", 0)
        posts = d.get("jobPostings", [])
        for j in posts:
            path = j.get("externalPath", "")
            out.append({"title": j.get("title", ""), "location": j.get("locationsText", ""),
                        "url": f"{base}/en-US/{site}{path}", "description": "",
                        "_wd": f"{base}/wday/cxs/{tenant}/{site}{path}"})
        offset += 20
        if not posts or offset >= (total or 0):
            break
    return out


def d_workday(api_url):
    r = get(api_url, headers={"Accept": "application/json"})
    r.raise_for_status()
    info = r.json().get("jobPostingInfo") or {}
    return html_to_text(info.get("jobDescription", ""))


def f_personio(slug):
    for tld in ("de", "com"):
        r = get(f"https://{slug}.jobs.personio.{tld}/xml")
        if r.status_code == 200:
            soup = BeautifulSoup(r.content, "xml")
            out = []
            for p in soup.find_all("position"):
                jid = p.find("id").get_text() if p.find("id") else ""
                desc = " ".join(html_to_text(v.get_text(), 1500) for v in p.find_all("value"))
                out.append({"title": clean(p.find("name").get_text() if p.find("name") else ""),
                            "location": clean(p.find("office").get_text() if p.find("office") else ""),
                            "url": f"https://{slug}.jobs.personio.{tld}/job/{jid}",
                            "description": clean(desc)[:3000]})
            return out
    r.raise_for_status()
    return []


def f_breezy(slug):
    r = get(f"https://{slug}.breezy.hr/json")
    r.raise_for_status()
    out = []
    for j in r.json():
        loc = j.get("location") or {}
        loc = loc.get("name", "") if isinstance(loc, dict) else str(loc)
        out.append({"title": j.get("name", ""), "location": loc, "url": j.get("url", ""), "description": ""})
    return out


def f_bamboohr(slug):
    r = get(f"https://{slug}.bamboohr.com/careers/list", headers={"Accept": "application/json"})
    r.raise_for_status()
    out = []
    for j in r.json().get("result", []):
        loc = j.get("location") or {}
        loc = ", ".join(x for x in [loc.get("city"), loc.get("state")] if x) if isinstance(loc, dict) else ""
        out.append({"title": j.get("jobOpeningName", ""), "location": loc,
                    "url": f"https://{slug}.bamboohr.com/careers/{j.get('id')}", "description": ""})
    return out


FETCHERS = {"greenhouse": f_greenhouse, "lever": f_lever, "workable": f_workable,
            "smartrecruiters": f_smartrecruiters, "ashby": f_ashby, "recruitee": f_recruitee,
            "teamtailor": f_teamtailor, "workday": f_workday, "personio": f_personio,
            "breezy": f_breezy, "bamboohr": f_bamboohr}


# --------------------------------------------------------------------------
# Generic careers-page parsing
# --------------------------------------------------------------------------
ROLE_WORD_RE = re.compile(
    r"\b(analyst|manager|engineer|executive|officer|specialist|coordinator|associate|assistant|"
    r"consultant|lead|developer|accountant|intern|internship|administrator|representative|"
    r"supervisor|director|designer|architect|advisor|adviser|technician|controller|planner|head|"
    r"agent|clerk|trainee|scientist|expert|strategist|auditor|buyer|merchandiser|recruiter|"
    r"owner|scrum master|operator|receptionist|secretary|lawyer|counsel|paralegal|nurse|teacher|"
    r"chef|driver|graduate)\b", re.I)
JOB_HREF_RE = re.compile(
    r"(/job/|/jobs/|/vacanc|/career/|/careers/|/position|/opening|/requisition|jobid=|job_id=|"
    r"/posting|/role/|/opportunit|/apply/|/jobdetail|/job-detail|/job-details)", re.I)
NAV_TEXT_RE = re.compile(
    r"^(careers?|jobs?|apply( now)?|view (all )?(jobs|openings|positions|vacancies)|search jobs|"
    r"home|about( us)?|contact( us)?|learn more|read more|see more|more|login|sign in|register|"
    r"join (us|our team)|life at .*|our (culture|people|values)|graduates?|internships?|"
    r"students?|faq|benefits|why .*|working (here|at .*)|current (openings|vacancies)|"
    r"open (positions|roles)|all jobs|job alerts?|talent community|privacy.*|cookie.*)$", re.I)
CAREERS_LINK_RE = re.compile(
    r"(careers?|jobs?\b|join[- ]?(us|our[- ]team)|work[- ](with|for)[- ]us|vacanc|"
    r"opportunit|recruit|talent|employment)", re.I)
ALL_JOBS_RE = re.compile(
    r"(view|see|browse|search|explore|find)( all)? (our )?(current )?(jobs|openings|positions|"
    r"vacancies|opportunities|roles)|current (openings|vacancies|opportunities)|open (positions|roles)|"
    r"job (openings|search|listings)|all jobs|join (us|our team)", re.I)
SPA_HINT_RE = re.compile(r"(id=\"root\"|id=\"app\"|__NEXT_DATA__|ng-version|data-reactroot|"
                         r"window\.__NUXT__|You need to enable JavaScript)", re.I)


def soup_of(r):
    return BeautifulSoup(r.text, "lxml")


def jsonld_jobs(soup, base_url):
    out = []
    for s in soup.find_all("script", type=re.compile("ld\\+json", re.I)):
        try:
            data = json.loads(s.string or s.get_text() or "")
        except Exception:  # noqa: BLE001
            continue
        stack = data if isinstance(data, list) else [data]
        while stack:
            d = stack.pop()
            if isinstance(d, list):
                stack.extend(d)
                continue
            if not isinstance(d, dict):
                continue
            if "@graph" in d:
                stack.extend(d["@graph"] if isinstance(d["@graph"], list) else [d["@graph"]])
            t = d.get("@type")
            if t == "JobPosting" or (isinstance(t, list) and "JobPosting" in t):
                loc = ""
                jl = d.get("jobLocation")
                jl = jl[0] if isinstance(jl, list) and jl else jl
                if isinstance(jl, dict):
                    a = jl.get("address") or {}
                    if isinstance(a, dict):
                        country = a.get("addressCountry")
                        if isinstance(country, dict):
                            country = country.get("name")
                        loc = ", ".join(x for x in [a.get("addressLocality"), a.get("addressRegion"),
                                                     country] if isinstance(x, str) and x)
                out.append({"title": clean(d.get("title", "")), "location": loc,
                            "url": urljoin(base_url, d.get("url", "") or base_url),
                            "description": html_to_text(d.get("description", ""))})
    return out


def nearby_location(a):
    """Location words in the job's own row/card (the largest ancestor, up to 4
    levels, that still contains only this one link)."""
    ctx, node = a, a
    for _ in range(4):
        node = node.parent
        if node is None or len(node.find_all("a", href=True)) > 1:
            break
        ctx = node
    txt = clean(ctx.get_text(" "))[:400]
    m = UAE_RE.search(txt)
    if m:
        return m.group(0)
    m = FOREIGN_RE.search(txt)
    return m.group(0) if m else ""


def anchor_jobs(soup, base_url):
    out, seen = [], set()
    base_host = urlparse(base_url).netloc.split(":")[0].removeprefix("www.")
    root_dom = ".".join(base_host.split(".")[-2:])
    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        if href.startswith(("mailto:", "tel:", "javascript:", "#")):
            continue
        url = urldefrag(urljoin(base_url, href))[0]
        if not url.startswith("http"):
            continue
        text = clean(a.get_text(" "))
        if not text:
            text = clean(a.get("title", "") or a.get("aria-label", ""))
        if len(text) < 4 or len(text) > 140 or NAV_TEXT_RE.match(text):
            continue
        host = urlparse(url).netloc.removeprefix("www.")
        same_site = host.endswith(root_dom) or detect_ats(url)[0] is not None
        if not same_site:
            continue
        role = ROLE_WORD_RE.search(text)
        hrefjob = JOB_HREF_RE.search(url)
        if not (role and (hrefjob or len(text.split()) <= 12)):
            continue
        if url.rstrip("/") == base_url.rstrip("/"):
            continue
        title = re.split(r"\s{2,}| \| | – .*(apply|location).*", text)[0][:140]
        key = (title.lower(), url)
        if key in seen:
            continue
        seen.add(key)
        out.append({"title": title, "location": nearby_location(a), "url": url, "description": ""})
    return out


def generic_jobs(page_url):
    """Return (jobs, reason). reason is None when the page was read."""
    if not allowed(page_url):
        return [], "robots.txt disallows"
    r = get(page_url)
    if r.status_code >= 400:
        return [], f"HTTP {r.status_code}"
    soup = soup_of(r)
    final = r.url
    jobs = jsonld_jobs(soup, final) + anchor_jobs(soup, final)
    if not jobs:
        # follow one "view all jobs" style link
        for a in soup.find_all("a", href=True):
            t = clean(a.get_text(" "))
            if ALL_JOBS_RE.search(t) or ALL_JOBS_RE.search(a["href"]):
                nxt = urldefrag(urljoin(final, a["href"]))[0]
                if nxt.rstrip("/") == final.rstrip("/") or not nxt.startswith("http"):
                    continue
                ats, key = detect_ats(nxt)
                if ats:
                    return FETCHERS[ats](key), None
                if not allowed(nxt):
                    break
                r2 = get(nxt)
                if r2.status_code < 400:
                    s2 = soup_of(r2)
                    ats, key = detect_ats(r2.url + " " + r2.text[:400000])
                    if ats:
                        return FETCHERS[ats](key), None
                    jobs = jsonld_jobs(s2, r2.url) + anchor_jobs(s2, r2.url)
                break
    if not jobs:
        text_len = len(clean(soup.get_text(" ")))
        uns = detect_unsupported(final + " " + r.text[:400000])
        if uns:
            return [], f"uses {uns} (not readable)"
        if SPA_HINT_RE.search(r.text[:400000]) and text_len < 2500:
            return [], "page needs JavaScript"
    return jobs, None


def d_generic(url):
    if not allowed(url):
        return ""
    r = get(url)
    if r.status_code >= 400:
        return ""
    soup = soup_of(r)
    for j in jsonld_jobs(soup, r.url):
        if j["description"]:
            return j["description"]
    for t in soup(["script", "style", "noscript", "nav", "header", "footer", "form"]):
        t.decompose()
    main = soup.find("main") or soup.find("article") or soup.body or soup
    return clean(main.get_text(" "))[:3000]


# --------------------------------------------------------------------------
# Discovery
# --------------------------------------------------------------------------
COMMON_PATHS = ["/careers", "/en/careers", "/careers/", "/jobs", "/en/jobs", "/join-us", "/en/join-us",
                "/work-with-us", "/career", "/en/career", "/about/careers", "/about-us/careers",
                "/en/about-us/careers", "/vacancies"]
CAREER_SIGNAL_RE = re.compile(r"(career|vacanc|job opening|open positions|current openings|"
                              r"join our team|work with us|apply now|opportunit)", re.I)


def fetch_home(domain):
    last = None
    for u in (f"https://{domain}", f"https://www.{domain}", f"http://{domain}"):
        try:
            r = get(u)
            if r.status_code < 400:
                return r
            last = f"HTTP {r.status_code}"
        except Exception as e:  # noqa: BLE001
            last = type(e).__name__
    raise RuntimeError(last or "unreachable")


def discover(company):
    """Return dict(status, careers_page, ats, ats_key, reason)."""
    domain = company["domain"]
    candidates = []
    if company.get("careers_url"):
        candidates.append(company["careers_url"])
    else:
        try:
            home = fetch_home(domain)
        except Exception as e:  # noqa: BLE001
            return {"status": "error", "reason": f"homepage: {e}"}
        blob = home.url + " " + home.text[:600000]
        ats, key = detect_ats(blob)
        if ats:
            return {"status": "found", "careers_page": home.url, "ats": ats, "ats_key": key}
        soup = soup_of(home)
        scored = []
        for a in soup.find_all("a", href=True):
            href = a["href"].strip()
            text = clean(a.get_text(" "))
            if not (CAREERS_LINK_RE.search(text) or CAREERS_LINK_RE.search(href)):
                continue
            url = urldefrag(urljoin(home.url, href))[0]
            if not url.startswith("http") or "linkedin.com" in url or "facebook.com" in url:
                continue
            ats, key = detect_ats(url)
            if ats:
                return {"status": "found", "careers_page": url, "ats": ats, "ats_key": key}
            score = 0
            if re.search(r"career", url + text, re.I):
                score += 3
            if re.search(r"jobs?|vacanc", url + text, re.I):
                score += 2
            if re.search(r"blog|news|article|press", url, re.I):
                score -= 4
            scored.append((score, url))
        scored.sort(key=lambda x: -x[0])
        for _, u in scored[:3]:
            if u not in candidates:
                candidates.append(u)
        base = f"{urlparse(home.url).scheme}://{urlparse(home.url).netloc}"
        candidates += [base + p for p in COMMON_PATHS]
        candidates += [f"https://careers.{domain}", f"https://jobs.{domain}"]
    tried = 0
    for u in candidates:
        if tried >= 8 or time_left() < 120:
            break
        tried += 1
        try:
            if not allowed(u):
                continue
            r = get(u)
        except Exception:  # noqa: BLE001
            continue
        if r.status_code >= 400:
            continue
        blob = r.url + " " + r.text[:600000]
        ats, key = detect_ats(blob)
        if ats:
            return {"status": "found", "careers_page": r.url, "ats": ats, "ats_key": key}
        if CAREER_SIGNAL_RE.search(BeautifulSoup(r.text[:600000], "lxml").get_text(" ")[:20000]):
            uns = detect_unsupported(blob)
            return {"status": "found", "careers_page": r.url,
                    "ats": f"unsupported:{uns}" if uns else "generic", "ats_key": ""}
    return {"status": "none", "reason": "no careers page found"}


# --------------------------------------------------------------------------
# Scan one company
# --------------------------------------------------------------------------
def scan_company(company, st):
    ats, key, page = st.get("ats"), st.get("ats_key"), st.get("careers_page")
    try:
        if ats in FETCHERS:
            raw = FETCHERS[ats](key)
            reason = None
        elif ats and ats.startswith("unsupported:"):
            raw, reason = generic_jobs(page)
            if not raw:
                reason = reason or f"uses {ats.split(':', 1)[1]} (not readable)"
        else:
            raw, reason = generic_jobs(page)
    except Exception as e:  # noqa: BLE001
        return {"ok": False, "reason": f"{type(e).__name__}: {str(e)[:120]}", "jobs": [], "raw_count": 0}
    if reason:
        return {"ok": False, "reason": reason, "jobs": [], "raw_count": 0}
    kept = []
    for j in raw:
        title = clean(j.get("title"))
        tier = tier_for(title)
        if not tier or not j.get("url"):
            continue
        if not location_ok(j.get("location", "")):
            continue
        j["title"], j["tier"] = title, tier
        kept.append(j)
    return {"ok": True, "jobs": kept, "raw_count": len(raw)}


def enrich_description(j):
    try:
        if j.get("_sr"):
            return d_smartrecruiters(*j["_sr"])
        if j.get("_wd"):
            return d_workday(j["_wd"])
        return d_generic(j["url"])
    except Exception:  # noqa: BLE001
        return ""


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------
def load_json(path, default):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except Exception:  # noqa: BLE001
        return default


def save_json(path, data, indent=None):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=indent)
    os.replace(tmp, path)


def load_companies():
    path = COMPANIES_CSV if os.path.exists(COMPANIES_CSV) else SEED_CSV
    with open(path, newline="", encoding="utf-8") as f:
        rows = [r for r in csv.DictReader(f) if r.get("domain")]
    seed_doms = set()
    if os.path.exists(SEED_CSV):
        with open(SEED_CSV, newline="", encoding="utf-8") as f:
            seed_doms = {r["domain"].strip().lower() for r in csv.DictReader(f) if r.get("domain")}
    for r in rows:
        r["domain"] = r["domain"].strip().lower()
        r["seed"] = r["domain"] in seed_doms
    return rows


def days_since(iso):
    if not iso:
        return 10_000
    try:
        return (NOW - datetime.strptime(iso, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)).days
    except ValueError:
        return 10_000


def job_key(company_domain, j):
    return urldefrag(j["url"])[0].rstrip("/").lower() or f"{company_domain}|{j['title'].lower()}"


def main():
    companies = load_companies()
    cstate = load_json(COMPANY_STATE, {})
    jobs_db = load_json(JOBS_DB, {})

    # ---- pick discovery work
    to_discover = []
    for c in companies:
        st = cstate.get(c["domain"], {})
        s = st.get("status")
        if s is None:
            to_discover.append(c)
        elif s == "none" and days_since(st.get("discovered_at")) >= REDISCOVER_NONE_DAYS:
            to_discover.append(c)
        elif s == "error" and days_since(st.get("discovered_at")) >= REDISCOVER_ERROR_DAYS:
            to_discover.append(c)
        elif c.get("careers_url") and st.get("careers_page") is None:
            to_discover.append(c)
    to_discover.sort(key=lambda c: (not c["seed"], cstate.get(c["domain"], {}).get("status") is not None))
    to_discover = to_discover[:DISCOVERY_PER_RUN]

    # ---- pick scan work (oldest scanned first, seed companies first on ties)
    discover_set = {c["domain"] for c in to_discover}
    scan_pool = [c for c in companies
                 if cstate.get(c["domain"], {}).get("status") == "found" and c["domain"] not in discover_set]
    scan_pool.sort(key=lambda c: (cstate[c["domain"]].get("last_scanned") or "", not c["seed"]))
    scan_list = scan_pool[:max(0, SCAN_PER_RUN - len(to_discover))]

    print(f"companies={len(companies)} discover={len(to_discover)} scan={len(scan_list)}", flush=True)

    scanned_today, with_jobs_today, unreadable, new_jobs = 0, 0, [], []
    lock = threading.Lock()

    def work(c, do_discover):
        if time_left() < 300:
            return c, None, None
        st = dict(cstate.get(c["domain"], {}))
        if do_discover:
            try:
                d = discover(c)
            except Exception as e:  # noqa: BLE001
                d = {"status": "error", "reason": f"{type(e).__name__}"}
            st.update({"status": d["status"], "discovered_at": NOW_ISO,
                       "careers_page": d.get("careers_page"), "ats": d.get("ats"),
                       "ats_key": d.get("ats_key"), "reason": d.get("reason")})
            if d["status"] != "found":
                return c, st, None
        if time_left() < 240:
            return c, st, None
        res = scan_company(c, st)
        return c, st, res

    def handle(c, st, res):
        nonlocal scanned_today, with_jobs_today
        if st is None:
            return
        with lock:
            if res is not None:
                scanned_today += 1
                st["last_scanned"] = NOW_ISO
                if res["ok"]:
                    st["last_ok"] = NOW_ISO
                    st["fail_count"] = 0
                    st["last_raw_count"] = res["raw_count"]
                    if res["jobs"]:
                        with_jobs_today += 1
                    for j in res["jobs"]:
                        k = job_key(c["domain"], j)
                        rec = jobs_db.get(k)
                        if rec is None:
                            rec = {"title": j["title"], "company": c["name"], "location": clean(j.get("location", "")),
                                   "url": j["url"], "careers_page": st.get("careers_page") or "",
                                   "tier": j["tier"], "first_seen": NOW_ISO,
                                   "description": j.get("description", "") or ""}
                            jobs_db[k] = rec
                            if not rec["description"]:
                                new_jobs.append((k, j))
                        rec["last_seen"] = NOW_ISO
                        rec["tier"] = j["tier"]
                        if j.get("location"):
                            rec["location"] = clean(j["location"])
                else:
                    st["fail_count"] = st.get("fail_count", 0) + 1
                    if st["fail_count"] >= 4:
                        # careers page probably moved: rediscover in ~10 days
                        st.update({"status": "error", "discovered_at": NOW_ISO, "fail_count": 0,
                                   "reason": "careers page failed 4 times in a row"})
                    unreadable.append({"name": c["name"], "careers_page": st.get("careers_page") or "",
                                       "reason": res["reason"]})
            cstate[c["domain"]] = st

    tasks = [(c, True) for c in to_discover] + [(c, False) for c in scan_list]
    with ThreadPoolExecutor(max_workers=WORKERS) as ex:
        futs = [ex.submit(work, c, d) for c, d in tasks]
        done = 0
        for f in as_completed(futs):
            try:
                handle(*f.result())
            except Exception:  # noqa: BLE001
                traceback.print_exc()
            done += 1
            if done % 100 == 0:
                print(f"  {done}/{len(tasks)} companies processed, {time_left()/60:.0f} min left", flush=True)
                save_json(COMPANY_STATE, cstate)

    # ---- descriptions for new jobs (tier 1 first)
    new_jobs.sort(key=lambda kj: kj[1]["tier"])
    new_jobs = new_jobs[:DESC_FETCH_LIMIT]
    if new_jobs and time_left() > 180:
        with ThreadPoolExecutor(max_workers=WORKERS) as ex:
            futs = {ex.submit(enrich_description, j): k for k, j in new_jobs}
            for f in as_completed(futs):
                if time_left() < 60:
                    break
                try:
                    desc = f.result()
                except Exception:  # noqa: BLE001
                    desc = ""
                if desc:
                    jobs_db[futs[f]]["description"] = desc[:3000]

    # ---- prune and write
    jobs_db = {k: v for k, v in jobs_db.items() if days_since(v.get("last_seen")) <= 90}
    feed = [dict(v) for v in jobs_db.values() if days_since(v.get("last_seen")) <= FEED_DAYS]
    feed.sort(key=lambda v: v.get("first_seen", ""), reverse=True)
    feed.sort(key=lambda v: v.get("tier", 9))
    feed = feed[:MAX_FEED_JOBS]

    found = [s for s in cstate.values() if s.get("status") == "found"]
    ats_counts = {}
    for s in found:
        a = (s.get("ats") or "generic").split(":")[0]
        ats_counts[a] = ats_counts.get(a, 0) + 1
    stats = {
        "companies_in_list": len(companies),
        "discovery_done": sum(1 for c in companies if cstate.get(c["domain"], {}).get("status")),
        "careers_pages_found": sum(1 for c in companies
                                   if cstate.get(c["domain"], {}).get("status") == "found"),
        "companies_scanned_today": scanned_today,
        "companies_with_relevant_jobs_today": with_jobs_today,
        "new_jobs_today": sum(1 for v in feed if days_since(v.get("first_seen")) < 1),
        "jobs_in_feed": len(feed),
        "tier1_jobs_in_feed": sum(1 for v in feed if v.get("tier") == 1),
        "unreadable_today": len(unreadable),
        "ats_breakdown": ats_counts,
        "runtime_minutes": round((time.time() - START) / 60, 1),
    }
    out = {"generated_at_utc": NOW_ISO, "stats": stats,
           "unreadable_companies_today": sorted(unreadable, key=lambda u: u["name"].lower()),
           "jobs": feed}
    save_json(OUT_FILE, out, indent=1)
    save_json(COMPANY_STATE, cstate)
    save_json(JOBS_DB, jobs_db)
    print(json.dumps(stats, indent=1))


if __name__ == "__main__":
    main()
