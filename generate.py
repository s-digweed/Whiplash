#!/usr/bin/env python3
"""
Whiplash + Eel EPG + M3U generator.

- Whiplash: single consolidated ErsatzTV feed (schedule.xml) with all channels
  incl. zén!th. Channels are remapped to stable local tvg-ids and copied as-is
  (proper XMLTV, no title surgery needed).
- Eel: eel.xml is title-only with wildly inconsistent episode formatting. Titles
  are parsed into <title> / <sub-title> / <episode-num> (onscreen + xmltv_ns) and
  run through a show-name rename table so IPTVBoss can format them per settings.

Outputs epg.xml (merged) and playlist.m3u. No deps beyond `requests`.
"""

import re
import os
import sys
import json
import time
import html
import requests
import xml.etree.ElementTree as ET

# ───────────────────────── Whiplash (single feed) ─────────────────────────
WL_URL = "https://whiplash.cc/scheds/schedule.xml"

# source ErsatzTV id -> (local tvg-id, display-name)
WL_CHANNEL_MAP = {
    "C1.1.146.ersatztv.org": ("whiplash",        "WHIPLASH"),
    "C2.1.147.ersatztv.org": ("whiplash2",       "WHIPLASH 2"),
    "C3.1.148.ersatztv.org": ("whiplashcinema",  "WHIPLASH CINEMA"),
    "C7.151.ersatztv.org":   ("whiplashatlas",   "WHIPLASH ATLAS"),
    "C3.147.ersatztv.org":   ("whiplashwindowtv","WHIPLASH WINDOW TV"),
    "C6.1.151.ersatztv.org": ("whiplashbiwi",    "BIWI"),
    "zenith":                ("whiplashzenith",  "ZÉN!TH"),
}
WL_LOGOS = {
    "whiplash":        "https://whiplash.cc/assets/img/channels/whiplash.png",
    "whiplash2":       "https://whiplash.cc/assets/img/channels/whiplash2.png",
    "whiplashcinema":  "https://whiplash.cc/assets/img/channels/whiplashcinema.png",
    "whiplashatlas":   "https://whiplash.cc/assets/img/channels/atlas.png",
    "whiplashwindowtv":"https://whiplash.cc/assets/img/channels/windowtv.png",
    "whiplashbiwi":    "https://whiplash.cc/assets/img/channels/biwi.png",
    "whiplashzenith":  "https://i.imgur.com/j63CKTM.png",
}
WL_STREAMS = {
    "whiplash":        "https://cdn.whiplash.cc/whiplash/index.m3u8",
    "whiplash2":       "https://cdn.whiplash.cc/whiplash-2/index.m3u8",
    "whiplashcinema":  "https://cdn.whiplash.cc/whiplash-cinema/index.m3u8",
    "whiplashatlas":   "https://cdn.whiplash.cc/whiplash-atlas/index.m3u8",
    "whiplashwindowtv":"https://cdn.whiplash.cc/whiplash-windowtv/index.m3u8",
    "whiplashbiwi":    "https://cdn.whiplash.cc/whiplash-biwi/index.m3u8",
    "whiplashzenith":  "https://cdn.whiplash.cc/whiplash-zenith/index.m3u8",
}
WL_M3U_ORDER = ["whiplash","whiplash2","whiplashatlas","whiplashcinema",
                "whiplashwindowtv","whiplashbiwi","whiplashzenith"]

# ───────────────────────────── Eel (normalized) ───────────────────────────
EEL_URL = "https://whiplash.cc/epg/eel.xml"
EEL_CHANNEL_MAP = {
    "C1.145.ersatztv.org": ("eel-channel",  "Eel Channel"),
    "C2.146.ersatztv.org": ("fizz",         "Fizz"),
    "C3.147.ersatztv.org": ("toon-diggity", "Toon Diggity"),
}
EEL_LOGOS = {
    "eel-channel":  "https://i.imgur.com/YBZUFXs.png",
    "fizz":         "https://i.imgur.com/0z5rG3A.png",
    "toon-diggity": "https://i.imgur.com/GhzJMF9.png",
}

# ── MistLive: copy every channel as-is, enrich only these two ──
MIST_URL = "https://api.mistlive.tv/api/xmltv.xml"
MIST_OUTPUT = "MistLive.xml"
MIST_ENRICH = {"vortex.iptv.mistlive.tv", "nfktv.iptv.mistlive.tv"}
# Show-name fixes for the enriched channels (display + metadata lookup).
MIST_RENAMES = {
    "The 70s Show":            "That '70s Show",
    "Malcom In The Middle":    "Malcolm in the Middle",
    "Genarator Rex":           "Generator Rex",
    "Courage The Cowardly Dog":"Courage the Cowardly Dog",
}

# Shows numbered ABSOLUTELY (3+ digit code = absolute ep in S01, hundreds kept)
ABSOLUTE_SHOWS = {"dragon ball"}

# Show-name renames, keyed on the parsed base title (trailing "(YYYY)" kept)
RENAMES = {
    "Garfield": "Garfield and Friends",
    "Batman The Animated Series": "Batman: The Animated Series",
    "Superman The Animated Series": "Superman: The Animated Series",
    "X-Men": "X-Men: The Animated Series",
    "Spider-Man": "Spider-Man: The Animated Series",
    "Eerie, Indiana - The Other Dimension": "Eerie, Indiana: The Other Dimension",
    "Sabrina TTW": "Sabrina the Teenage Witch",
    "Adventures Of Sonic The Hedgehog": "Adventures of Sonic the Hedgehog",
    "SOUTH PARK": "South Park",
    "DOUG": "Disney's Doug",
    "Sabrina The Animated Series": "Sabrina: The Animated Series",
    "Andy Milonakis Show": "The Andy Milonakis Show",
    "Secret World Of Alex Mack": "The Secret World of Alex Mack",
    "Bill Nye The Science Guy": "Bill Nye the Science Guy",
    "Homeless In Denton": "Homeless in Denton",
    "Shin-Chan": "Crayon Shin-chan",
    "Chip n' Dale Rescue Rangers": "Chip 'n Dale Rescue Rangers",
    "Oban Star-Racers": "Ōban Star-Racers",
    # parked (not in current feed, kept in case the source drifts):
    "It's Always Sunny at": "It's Always Sunny in Philadelphia",
    "Batman Animated": "Batman: The Animated Series",
    "Superman Animated": "Superman: The Animated Series",
    "The Grim Adv. of Billy & Mandy": "The Grim Adventures of Billy & Mandy",
    "Eerie, Indiana: Other": "Eerie, Indiana: The Other Dimension",
    "Mighty Mouse '87": "Mighty Mouse: The New Adventures (1987)",
    "SRMTHFG!": "Super Robot Monkey Team Hyperforce Go!",
}

# Fuzzy renames: (pattern, canonical) applied when the exact table misses.
# Catches truncated / variant titles, e.g. a bare "It's Always Sunny".
REGEX_RENAMES = [
    (re.compile(r"^It[\u2019']?s\s+Always\s+Sunny\b.*$", re.I),
     "It's Always Sunny in Philadelphia"),
]

# Fixed descriptions for block/filler programmes with no episode data (keyed by title).
_FIZZ_MIX_DESC = ("Classic cartoons like Looney Tunes, Tom and Jerry, Woody Woodpecker, "
                  "Droopy, NFB Canada and Zagreb Film animated shorts plus some "
                  "Pop and Rock music videos.")
_TOON_DISNEY_DESC = "Timeless theatrical animated shorts from Disney's golden age."
FIXED_DESC = {
    "Late Night Mix":     _FIZZ_MIX_DESC,
    "Evening Mix":        _FIZZ_MIX_DESC,
    "Toon Disney Shorts": _TOON_DISNEY_DESC,
}

# ── title parser ──
YEAR_ANY = re.compile(r'\((?:19|20)\d\d\)')
YEAR_END = re.compile(r'\s*(\((?:19|20)\d\d\))\s*$')
STRONG = re.compile(
    r'(?<![A-Za-z0-9])'
    r'(?:S(\d{1,2})\s*E[Pp]?\s*(\d{1,2})(?:\s*-\s*E?(\d{1,2}))?'
    r'|(\d{1,2})x(\d{1,2})(?:-(\d{1,2}))?)'
    r'(?![A-Za-z0-9])', re.I)
EP_MARK  = re.compile(r'(?<![A-Za-z0-9])E[Pp][Ss]?\s*(\d{2,4})(?![A-Za-z0-9])')
P_NdashN = re.compile(r'(?:^|\s)(\d{1,2})-(\d{2})$')
P_EPISODE= re.compile(r'(?:^|\s)Episode\s+(\d+)$', re.I)
P_DIGITS = re.compile(r'(?:^|\s)T?(\d{2,4})$')
P_TFRONT = re.compile(r'^T(\d{2,4})\s+(\S.*)$')

def _digits_to_se(d, show):
    if show.strip().lower() in ABSOLUTE_SHOWS: return 1, int(d)
    if len(d) == 2: return 1, int(d)
    if len(d) == 3: return (1, int(d[1:])) if d[0] == '0' else (int(d[0]), int(d[1:]))
    if len(d) == 4: return int(d[:2]), int(d[2:])
    return 1, int(d)

def _clean(s):
    s = re.sub(r'^[\s_\-]+|[\s_\-]+$', '', s.strip())
    return re.sub(r'\s{2,}', ' ', s).strip()

def _rename(title):
    m = YEAR_END.search(title)
    yr = " " + m.group(1) if m else ""
    base = title[:m.start()].strip() if m else title
    if base in RENAMES:
        base = RENAMES[base]
    else:
        for rx, canon in REGEX_RENAMES:
            if rx.match(base):
                base = canon
                yr = ""          # canonical already carries any year it needs
                break
    return (base + yr).strip()

def parse_title(raw):
    """Return (title, subtitle_or_None, season_or_None, ep_or_None, ep_end_or_None)."""
    t = html.unescape(raw).strip().replace('_', ' - ')
    t = re.sub(r'\s{2,}', ' ', t)
    title, subtitle, season, ep, ep_end = t, None, None, None, None

    m = STRONG.search(t)
    if m:
        if m.group(1):
            season, ep = int(m.group(1)), int(m.group(2))
            ep_end = int(m.group(3)) if m.group(3) else None
        else:
            season, ep = int(m.group(4)), int(m.group(5))
            ep_end = int(m.group(6)) if m.group(6) else None
        title = _clean(t[:m.start()])
        subtitle = _clean(YEAR_ANY.sub('', t[m.end():])) or None
        return _rename(title), subtitle, season, ep, ep_end

    m = EP_MARK.search(t)
    if m:
        show = _clean(t[:m.start()])
        season, ep = _digits_to_se(m.group(1), show)
        subtitle = _clean(YEAR_ANY.sub('', t[m.end():])) or None
        return _rename(show), subtitle, season, ep, None

    segs = re.split(r'\s+-\s+', t)
    def peel(front):
        for rx, kind in ((P_NdashN,'nd'),(P_EPISODE,'ep'),(P_DIGITS,'dig')):
            mm = rx.search(front)
            if not mm: continue
            pref = front[:mm.start()].strip()
            if kind == 'nd': return pref, int(mm.group(1)), int(mm.group(2))
            if kind == 'ep': return pref, 1, int(mm.group(1))
            se, e = _digits_to_se(mm.group(1), pref); return pref, se, e
        return None
    if len(segs) >= 2:
        c = peel(segs[-1].strip())
        if c and c[0] == '':
            _, season, ep = c; title = _clean(" - ".join(segs[:-1]))
        else:
            subtitle = segs[-1].strip()
            c = peel(" - ".join(segs[:-1]))
            if c: title, season, ep = _clean(c[0]), c[1], c[2]
            else: title = _clean(" - ".join(segs[:-1]))
    else:
        c = peel(t)
        if c: title, season, ep = _clean(c[0]), c[1], c[2]
        else:
            fm = P_TFRONT.match(t)
            if fm:
                season, ep = _digits_to_se(fm.group(1), fm.group(2))
                title = _clean(fm.group(2))
    return _rename(title), subtitle, season, ep, ep_end


# ───────────────────────── TMDB episode descriptions ──────────────────────
# Optional: set the TMDB_API_KEY env (GitHub Secret). If absent, descriptions
# are simply skipped and the EPG is generated exactly as before.
TMDB_KEY        = os.environ.get("TMDB_API_KEY", "").strip()
TMDB_BASE       = "https://api.themoviedb.org/3"
TMDB_LANG       = "en-US"
DESC_CACHE_FILE = "desc_cache.json"

# Force a TMDB show id when search picks the wrong one: {"Show Name": 1234}
SHOW_TMDB_OVERRIDES = {}

_QYEAR = re.compile(r'\s*\(((?:19|20)\d\d)\)\s*$')
_tmdb_session = requests.Session()

def load_desc_cache():
    try:
        with open(DESC_CACHE_FILE, encoding="utf-8") as f:
            c = json.load(f)
            for k in ("shows","episodes","tvmaze_shows","tvmaze_episodes","tmdb_seasons",
                      "tvmaze_eplist","tvdb_shows","tvdb_episodes",
                      "tvmaze_namemap","tvdb_namemap","tmdb_movies"):
                c.setdefault(k, {})
            if not c.get("_tvdb_v2"):                    # refresh TVDB layer once (/eng + slug overrides)
                c["tvdb_shows"] = {}; c["tvdb_episodes"] = {}; c["_tvdb_v2"] = True
            if not c.get("_meta_v3"):                    # refresh episode caches once to capture episode NAMES
                for _k in ("episodes","tvmaze_episodes","tvdb_episodes","tvmaze_eplist"): c[_k] = {}
                c["_meta_v3"] = True
            return c
    except Exception:
        return {"shows": {}, "episodes": {}, "tvmaze_shows": {}, "tvmaze_episodes": {},
                "tmdb_seasons": {}, "tvmaze_eplist": {}, "tvdb_shows": {}, "tvdb_episodes": {},
                "tvmaze_namemap": {}, "tvdb_namemap": {}, "tmdb_movies": {}}

def save_desc_cache(cache):
    with open(DESC_CACHE_FILE, "w", encoding="utf-8") as f:
        json.dump(cache, f, ensure_ascii=False, indent=0, sort_keys=True)

def _tmdb_get(path, **params):
    params["api_key"] = TMDB_KEY
    for _ in range(3):
        try:
            r = _tmdb_session.get(TMDB_BASE + path, params=params, timeout=20)
            if r.status_code == 429:
                time.sleep(int(r.headers.get("Retry-After", "2")) + 1); continue
            return r.json() if r.status_code == 200 else None
        except requests.RequestException:
            time.sleep(1)
    return None

def _resolve_show_id(show, cache):
    if show in SHOW_TMDB_OVERRIDES:
        return SHOW_TMDB_OVERRIDES[show]
    key = show.lower()
    if key in cache["shows"]:
        return cache["shows"][key]                       # may be None = "searched, not found"
    ym = _QYEAR.search(show)
    query = show[:ym.start()].strip() if ym else show
    params = {"query": query}
    if ym: params["first_air_date_year"] = ym.group(1)
    data = _tmdb_get("/search/tv", **params)
    sid = data["results"][0]["id"] if (data and data.get("results")) else None
    cache["shows"][key] = sid
    return sid

def _rec(v):
    """Normalize a cached episode value -> (overview, name). Legacy str = overview only."""
    if isinstance(v, dict):
        return (v.get("o") or ""), (v.get("n") or "")
    return (v or ""), ""

def _tmdb_meta(show, season, ep, cache):
    if not TMDB_KEY:
        return "", ""
    sid = _resolve_show_id(show, cache)
    if not sid:
        return "", ""
    ck = f"{sid}|{season}|{ep}"
    if ck in cache["episodes"]:
        return _rec(cache["episodes"][ck])
    data = _tmdb_get(f"/tv/{sid}/season/{season}/episode/{ep}", language=TMDB_LANG)
    ov = ((data or {}).get("overview") or "").strip()
    nm = ((data or {}).get("name") or "").strip()
    cache["episodes"][ck] = {"o": ov, "n": nm}
    return ov, nm

# ── TVmaze fallback (keyless) ──
ENABLE_TVMAZE = True
TVMAZE_BASE   = "https://api.tvmaze.com"
_TAGS = re.compile(r"<[^>]+>")

def _tvmaze_get(path, **params):
    for _ in range(3):
        try:
            r = _tmdb_session.get(TVMAZE_BASE + path, params=params, timeout=20)
            time.sleep(0.2)                               # ~5 req/s: well under TVmaze's limit
            if r.status_code == 429:
                time.sleep(int(r.headers.get("Retry-After", "5")) + 1); continue
            if r.status_code == 200:
                return r.json()
            return None                                  # 404 = no such episode
        except requests.RequestException:
            time.sleep(1)
    return None

def _resolve_tvmaze_id(show, cache):
    key = show.lower()
    if key in cache["tvmaze_shows"]:
        return cache["tvmaze_shows"][key]
    ym = _QYEAR.search(show)
    query = show[:ym.start()].strip() if ym else show
    data = _tvmaze_get("/singlesearch/shows", q=query)
    tid = data.get("id") if isinstance(data, dict) else None
    cache["tvmaze_shows"][key] = tid
    return tid

def _tvmaze_meta(show, season, ep, cache):
    tid = _resolve_tvmaze_id(show, cache)
    if not tid:
        return "", ""
    ck = f"{tid}|{season}|{ep}"
    if ck in cache["tvmaze_episodes"]:
        return _rec(cache["tvmaze_episodes"][ck])
    data = _tvmaze_get(f"/shows/{tid}/episodebynumber", season=season, number=ep)
    d = data if isinstance(data, dict) else {}
    ov = html.unescape(_TAGS.sub("", d.get("summary") or "")).strip()
    nm = (d.get("name") or "").strip()
    cache["tvmaze_episodes"][ck] = {"o": ov, "n": nm}
    return ov, nm

def _tvmaze_eplist(tid, cache):
    """Flat list of regular-episode summaries in air order (index 0 = ep 1). Cached."""
    key = str(tid)
    if key in cache["tvmaze_eplist"]:
        return cache["tvmaze_eplist"][key]
    data = _tvmaze_get(f"/shows/{tid}/episodes")
    lst = []
    if isinstance(data, list):
        for e in data:
            if e.get("season") and e.get("number"):          # skip specials
                lst.append({"o": html.unescape(_TAGS.sub("", e.get("summary") or "")).strip(),
                            "n": (e.get("name") or "").strip()})
    cache["tvmaze_eplist"][key] = lst
    return lst

def _tmdb_seasons(sid, cache):
    """[[season_number, episode_count], ...] for regular seasons. Cached."""
    key = str(sid)
    if key in cache["tmdb_seasons"]:
        return cache["tmdb_seasons"][key]
    data = _tmdb_get(f"/tv/{sid}")
    seasons = []
    if data:
        for s in data.get("seasons", []):
            if s.get("season_number", 0) >= 1 and s.get("episode_count"):
                seasons.append([s["season_number"], s["episode_count"]])
    seasons.sort()
    cache["tmdb_seasons"][key] = seasons
    return seasons

def _absolute_meta(show, absN, cache):
    """Treat absN as an ABSOLUTE episode number and resolve via the show's episode list."""
    if not absN or absN < 1:
        return "", ""
    tid = cache["tvmaze_shows"].get(show.lower())               # set during the TVmaze direct try
    if tid:
        lst = _tvmaze_eplist(tid, cache)
        if 1 <= absN <= len(lst):
            o, n = _rec(lst[absN - 1])
            if o or n:
                return o, n
    sid = _resolve_show_id(show, cache) if TMDB_KEY else None
    if sid:
        rem = absN
        for snum, cnt in _tmdb_seasons(sid, cache):
            if rem <= cnt:
                ck = f"{sid}|{snum}|{rem}"
                if ck not in cache["episodes"]:
                    data = _tmdb_get(f"/tv/{sid}/season/{snum}/episode/{rem}", language=TMDB_LANG)
                    cache["episodes"][ck] = {"o": ((data or {}).get("overview") or "").strip(),
                                             "n": ((data or {}).get("name") or "").strip()}
                return _rec(cache["episodes"][ck])
            rem -= cnt
    return "", ""

# ── TheTVDB fallback (third source; strong on old-cartoon episode overviews) ──
TVDB_KEY   = os.environ.get("TVDB_API_KEY", "").strip()
TVDB_BASE  = "https://api4.thetvdb.com/v4"
ENABLE_TVDB = bool(TVDB_KEY)
_TVDB_TOKEN = None

def _tvdb_login():
    global _TVDB_TOKEN
    if not TVDB_KEY:
        return None
    try:
        r = _tmdb_session.post(TVDB_BASE + "/login", json={"apikey": TVDB_KEY}, timeout=20)
        _TVDB_TOKEN = r.json().get("data", {}).get("token") if r.status_code == 200 else None
    except requests.RequestException:
        _TVDB_TOKEN = None
    return _TVDB_TOKEN

def _tvdb_get(path, **params):
    global _TVDB_TOKEN
    if not TVDB_KEY:
        return None
    if _TVDB_TOKEN is None and _tvdb_login() is None:
        return None
    for attempt in range(2):
        try:
            r = _tmdb_session.get(TVDB_BASE + path, params=params,
                                  headers={"Authorization": f"Bearer {_TVDB_TOKEN}"}, timeout=20)
            if r.status_code == 401 and attempt == 0:
                _TVDB_TOKEN = None
                if _tvdb_login() is None:
                    return None
                continue
            return r.json().get("data") if r.status_code == 200 else None
        except requests.RequestException:
            time.sleep(1)
    return None

# Force a TVDB series by its thetvdb.com slug (from the URL) when search mismatches.
SHOW_TVDB_OVERRIDES = {
    "Spider-Man: The Animated Series": "spider-man-1994",
}

def _tvdb_search_id(query):
    data = _tvdb_get("/search", query=query, type="series")
    if isinstance(data, list) and data:
        return data[0].get("tvdb_id") or data[0].get("id")
    return None

def _resolve_tvdb_id(show, cache):
    if show in SHOW_TVDB_OVERRIDES:
        slug = SHOW_TVDB_OVERRIDES[show]
        ck = "slug:" + slug
        if ck in cache["tvdb_shows"]:
            return cache["tvdb_shows"][ck]
        d = _tvdb_get(f"/series/slug/{slug}")
        tid = d.get("id") if isinstance(d, dict) else None
        cache["tvdb_shows"][ck] = tid
        return tid
    key = show.lower()
    if key in cache["tvdb_shows"]:
        return cache["tvdb_shows"][key]
    ym = _QYEAR.search(show)
    query = show[:ym.start()].strip() if ym else show
    tid = _tvdb_search_id(query)
    if tid is None and ":" in query:                     # retry on the base name
        tid = _tvdb_search_id(query.split(":")[0].strip())
    cache["tvdb_shows"][key] = tid
    return tid

def _tvdb_meta(show, season, ep, cache):
    if not ENABLE_TVDB:
        return "", ""
    tid = _resolve_tvdb_id(show, cache)
    if not tid:
        return "", ""
    ck = f"{tid}|{season}|{ep}"
    if ck in cache["tvdb_episodes"]:
        return _rec(cache["tvdb_episodes"][ck])
    ov = nm = ""
    for path in (f"/series/{tid}/episodes/default/eng", f"/series/{tid}/episodes/default"):
        data = _tvdb_get(path, season=season, episodeNumber=ep, page=0)
        eps = data.get("episodes") if isinstance(data, dict) else None
        if isinstance(eps, list) and eps:
            m = next((e for e in eps if e.get("seasonNumber") == season and e.get("number") == ep), eps[0])
            ov = (m.get("overview") or "").strip()
            if not nm:
                nm = (m.get("name") or "").strip()
            if ov:
                break
    cache["tvdb_episodes"][ck] = {"o": ov, "n": nm}
    return ov, nm

def _norm(name):
    return re.sub(r"[^a-z0-9]+", " ", (name or "").lower()).strip()

def _tvmaze_namemap(tid, cache):
    key = str(tid)
    if key in cache["tvmaze_namemap"]:
        return cache["tvmaze_namemap"][key]
    data = _tvmaze_get(f"/shows/{tid}/episodes")
    m = {}
    if isinstance(data, list):
        for e in data:
            nm = _norm(e.get("name")); sn = e.get("season"); num = e.get("number")
            if nm and sn and num:
                m.setdefault(nm, [sn, num])
    cache["tvmaze_namemap"][key] = m
    return m

def _tvdb_namemap(tid, cache):
    key = str(tid)
    if key in cache["tvdb_namemap"]:
        return cache["tvdb_namemap"][key]
    m = {}
    for page in range(10):                               # safety cap; 500 eps/page
        data = _tvdb_get(f"/series/{tid}/episodes/default/eng", page=page)
        eps = data.get("episodes") if isinstance(data, dict) else None
        if not eps:
            break
        for e in eps:
            nm = _norm(e.get("name")); sn = e.get("seasonNumber"); num = e.get("number")
            if nm and sn and num:
                m.setdefault(nm, [sn, num])
        if len(eps) < 100:
            break
    cache["tvdb_namemap"][key] = m
    return m

def _name_to_se(show, name, cache):
    """Match an episode NAME to its (season, number) via the show's episode list."""
    target = _norm(name)
    if not target:
        return None, None
    if ENABLE_TVMAZE:
        tid = _resolve_tvmaze_id(show, cache)
        if tid:
            se = _tvmaze_namemap(tid, cache).get(target)
            if se:
                return se[0], se[1]
    if ENABLE_TVDB:
        tid = _resolve_tvdb_id(show, cache)
        if tid:
            se = _tvdb_namemap(tid, cache).get(target)
            if se:
                return se[0], se[1]
    return None, None

def episode_meta(show, season, ep, cache):
    """(overview, name): first non-empty of each across sources. Cached; never raises."""
    if season is None:
        return None, None
    ov = nm = ""
    def take(res):
        nonlocal ov, nm
        o, n = res
        if o and not ov: ov = o
        if n and not nm: nm = n
        return bool(ov and nm)
    if take(_tmdb_meta(show, season, ep, cache)):                 return ov, nm
    if ENABLE_TVMAZE and take(_tvmaze_meta(show, season, ep, cache)): return ov, nm
    if ENABLE_TVDB and take(_tvdb_meta(show, season, ep, cache)):     return ov, nm
    if season == 1: take(_absolute_meta(show, ep, cache))
    return (ov or None), (nm or None)

def episode_overview(show, season, ep, cache):
    return episode_meta(show, season, ep, cache)[0]

# ── XML helpers ──
_XML_ILLEGAL = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]")
_LOCAL_IP = re.compile(r'^(https?://)?(192\.168\.|10\.|172\.(1[6-9]|2[0-9]|3[01])\.)')
HEADERS = {"User-Agent": "Mozilla/5.0 (compatible; WhiplashEPGBot/1.0)"}
# Full browser headers for servers that WAF-block bot user-agents (e.g. MistLive 403).
BROWSER_HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36"),
    "Accept": "application/xml,text/xml,*/*;q=0.9",
    "Accept-Language": "en-US,en;q=0.9",
}

def _sanitize(text): return _XML_ILLEGAL.sub("", text)

def _strip_local_images(prog):
    for tag in ("icon", "image"):
        for elem in list(prog.findall(tag)):
            src = elem.get("src") or elem.text or ""
            if _LOCAL_IP.search(src.strip()): prog.remove(elem)
    return prog

def fetch_xml(url, headers=None):
    resp = requests.get(url, headers=headers or HEADERS, timeout=30); resp.raise_for_status()
    return ET.fromstring(_sanitize(resp.content.decode("utf-8-sig", errors="replace")))

def fetch_xml_safe(url, name, headers=None):
    try: return fetch_xml(url, headers=headers)
    except (ET.ParseError, requests.RequestException) as e:
        print(f"WARNING: {name} fetch/parse error ({e}) - skipping {name} this run")
        return ET.fromstring("<tv></tv>")

def _http_diag(name, status, hdrs):
    """Log why a fetch was refused (Cloudflare / IP block / auth) instead of guessing."""
    keys = ("server", "cf-ray", "cf-mitigated", "cf-cache-status", "retry-after",
            "www-authenticate", "x-sucuri-id")
    shown = {k: hdrs.get(k) for k in keys if hdrs.get(k)}
    print(f"  {name} HTTP {status} | {shown or 'no telltale headers'}")

def fetch_mist(url):
    """MistLive sits behind bot protection. Try a TLS-impersonating client (curl_cffi,
    real-Chrome handshake) first, then fall back to plain requests. Return root or <tv/>."""
    try:
        from curl_cffi import requests as creq
        r = creq.get(url, impersonate="chrome", timeout=30)
        if r.status_code == 200:
            print("  fetched via curl_cffi (chrome impersonation)")
            return ET.fromstring(_sanitize(r.content.decode("utf-8-sig", errors="replace")))
        _http_diag("MistLive(curl_cffi)", r.status_code, r.headers)
    except ImportError:
        print("  curl_cffi not installed - falling back to requests")
    except Exception as e:
        print(f"  curl_cffi attempt failed: {e}")
    try:
        r = requests.get(url, headers=BROWSER_HEADERS, timeout=30)
        if r.status_code == 200:
            return ET.fromstring(_sanitize(r.content.decode("utf-8-sig", errors="replace")))
        _http_diag("MistLive(requests)", r.status_code, r.headers)
    except (ET.ParseError, requests.RequestException) as e:
        print(f"  requests attempt failed: {e}")
    print("WARNING: MistLive unavailable - skipping MistLive this run")
    return ET.fromstring("<tv></tv>")

def add_channels(tv, chan_map, logos):
    for _, (local_id, display) in chan_map.items():
        if tv.find(f"./channel[@id='{local_id}']") is not None: continue
        ch = ET.SubElement(tv, "channel", {"id": local_id})
        ET.SubElement(ch, "display-name").text = display
        if local_id in logos: ET.SubElement(ch, "icon", {"src": logos[local_id]})

_ONSCR_SPACE = re.compile(r"\bS(\d+)E(\d+)")

def _space_onscreen(prog):
    """Reformat onscreen episode-num 'SxxEyy' -> 'Sxx Eyy' (xmltv_ns left untouched)."""
    for en in prog.findall("episode-num"):
        if en.get("system") == "onscreen" and en.text:
            en.text = _ONSCR_SPACE.sub(r"S\1 E\2", en.text)

def copy_whiplash(tv, root):
    for src_id, (local_id, _) in WL_CHANNEL_MAP.items():
        n = 0
        for prog in root.findall("programme"):
            if prog.get("channel") != src_id: continue
            np = ET.fromstring(ET.tostring(prog)); np.set("channel", local_id)
            _strip_local_images(np); _space_onscreen(np); tv.append(np); n += 1
        if n: print(f"  {local_id}: {n} programmes")

def build_eel(tv, root, cache):
    got_desc = got_sub = 0
    for src_id, (local_id, _) in EEL_CHANNEL_MAP.items():
        n = 0
        for prog in root.findall("programme"):
            if prog.get("channel") != src_id: continue
            raw_title = (prog.findtext("title") or "").strip()
            title, sub, season, ep, ep_end = parse_title(raw_title)
            desc = None
            if season is None and sub:                 # have episode name, no number -> match it
                season, ep = _name_to_se(title, sub, cache)
            if season is not None:
                desc, epname = episode_meta(title, season, ep, cache)
                if not sub and epname:                 # fill missing episode name from metadata
                    sub = epname; got_sub += 1
            if desc is None and title in FIXED_DESC:    # fixed desc for block/filler programmes
                desc = FIXED_DESC[title]
            np = ET.Element("programme", {k: prog.get(k) for k in prog.keys()})
            np.set("channel", local_id)
            ET.SubElement(np, "title", {"lang": "en"}).text = title
            if sub: ET.SubElement(np, "sub-title", {"lang": "en"}).text = sub
            if desc:
                ET.SubElement(np, "desc", {"lang": "en"}).text = desc
                got_desc += 1
            if season is not None:
                onscr = f"S{season:02d} E{ep:02d}" + (f"-E{ep_end:02d}" if ep_end else "")
                ET.SubElement(np, "episode-num", {"system": "onscreen"}).text = onscr
                ET.SubElement(np, "episode-num", {"system": "xmltv_ns"}).text = f"{season-1}.{ep-1}."
            tv.append(np); n += 1
        if n: print(f"  {local_id}: {n} programmes (normalized)")
    if TMDB_KEY: print(f"  descriptions attached: {got_desc} | episode names added: {got_sub}")

_MIST_DASH_SE = re.compile(r"S(\d{1,2})\s*[-–]\s*E(\d{1,2})", re.I)  # "S1 - E5" -> S1E5
_MIST_EPISODE = re.compile(r"episode[\s\-_]*(\d{1,3})", re.I)             # "...episode-17..."
_MIST_LEADNUM = re.compile(r"^(\d{1,2})\s+\D")                            # "10 Damien" -> ep 10

def _mist_se(sub):
    """Extract (season, ep) from a MistLive sub-title. None,None if not episodic."""
    if not sub:
        return None, None
    s = sub.replace("+", " ").replace("_", " ").replace(".", " ")
    s = re.sub(r"\s+", " ", s).strip()
    s = _MIST_DASH_SE.sub(lambda m: f"S{m.group(1)}E{m.group(2)}", s)
    _, _, season, ep, _ = parse_title(s)
    if season is not None:
        return season, ep
    m = _MIST_EPISODE.search(s)                 # bare "episode N" -> S01E N (absolute walk fixes season)
    if m:
        return 1, int(m.group(1))
    m = _MIST_LEADNUM.match(s)                  # leading "NN Title" -> S01E NN
    if m:
        return 1, int(m.group(1))
    return None, None

def _mist_lookup_name(title):
    """Show name for metadata lookup: drop parenthetical tags, apply renames."""
    name = MIST_RENAMES.get(title, title)
    return re.sub(r"\s*\([^)]*\)\s*", " ", name).strip() or name

_MV_MARKER = re.compile(r"(official|music|lyric)\s*(video|visualizer|audio)|\bvisualizer\b", re.I)

def _movie_meta(raw_title, cache):
    """Look up a non-episodic title as a MOVIE on TMDB. Returns (year, overview) or (None,None).
    Strict: exact normalized-title match + real vote count, so music videos/art shorts never match."""
    if not TMDB_KEY:
        return None, None
    if _MV_MARKER.search(raw_title) or " - " in raw_title:   # music video / "Artist - Title" -> not a movie
        return None, None
    ym = re.search(r"\((19|20)\d\d\)", raw_title)
    year = ym.group(0)[1:-1] if ym else None
    clean = re.sub(r"\s*[\(\[][^\)\]]*[\)\]]\s*", " ", raw_title)   # drop (…) and […]
    clean = re.sub(r"\s+", " ", clean).strip()
    if not clean:
        return None, None
    key = clean.lower() + (f"|{year}" if year else "")
    if key in cache["tmdb_movies"]:
        rec = cache["tmdb_movies"][key]
        return (rec["y"], rec["o"]) if rec else (None, None)
    params = {"query": clean}
    if year: params["year"] = year
    data = _tmdb_get("/search/movie", **params) or {}
    rec = None
    for res in (data.get("results") or [])[:5]:
        if _norm(res.get("title")) == _norm(clean) and (res.get("vote_count") or 0) >= 50:
            rd = res.get("release_date") or ""
            rec = {"y": rd[:4] if rd[:4].isdigit() else (year or ""),
                   "o": (res.get("overview") or "").strip()}
            break
    cache["tmdb_movies"][key] = rec
    return (rec["y"], rec["o"]) if rec else (None, None)

def build_mist(root, cache):
    """Copy every channel/programme as-is; enrich only the MIST_ENRICH channels."""
    tv = ET.Element("tv", {"generator-info-name": "mistlive-epg-generator"})
    for ch in root.findall("channel"):
        tv.append(ET.fromstring(ET.tostring(ch)))
    kept = enriched = movies = got_desc = got_sub = 0
    for prog in root.findall("programme"):
        cid = prog.get("channel")
        if cid not in MIST_ENRICH:
            tv.append(ET.fromstring(ET.tostring(prog))); kept += 1
            continue
        raw_title = (prog.findtext("title") or "").strip()
        disp_title = MIST_RENAMES.get(raw_title, raw_title)   # keep content tags, fix names
        season, ep = _mist_se(prog.findtext("sub-title"))
        sub = desc = None
        if season is not None:
            lookup = _mist_lookup_name(raw_title)
            desc, epname = episode_meta(lookup, season, ep, cache)
            if epname: sub = epname; got_sub += 1
        if season is None:                                   # not a TV episode -> try MOVIE
            m_year, m_desc = _movie_meta(raw_title, cache)
            if m_year or m_desc:
                np = ET.Element("programme", {k: prog.get(k) for k in prog.keys()})
                mt = disp_title
                if m_year and not re.search(r"\((19|20)\d\d\)", mt):
                    mt = f"{mt} ({m_year})"
                ET.SubElement(np, "title", {"lang": "en"}).text = mt
                if m_desc: ET.SubElement(np, "desc", {"lang": "en"}).text = m_desc
                if m_year: ET.SubElement(np, "date").text = m_year
                ET.SubElement(np, "category", {"lang": "en"}).text = "Movie"
                tv.append(np); movies += 1
            else:                                            # music video / art short -> leave as-is
                tv.append(ET.fromstring(ET.tostring(prog))); kept += 1
            continue
        np = ET.Element("programme", {k: prog.get(k) for k in prog.keys()})
        ET.SubElement(np, "title", {"lang": "en"}).text = disp_title
        if sub: ET.SubElement(np, "sub-title", {"lang": "en"}).text = sub
        if desc:
            ET.SubElement(np, "desc", {"lang": "en"}).text = desc; got_desc += 1
        onscr = f"S{season:02d} E{ep:02d}"
        ET.SubElement(np, "episode-num", {"system": "onscreen"}).text = onscr
        ET.SubElement(np, "episode-num", {"system": "xmltv_ns"}).text = f"{season-1}.{ep-1}."
        tv.append(np); enriched += 1
    print(f"  copied as-is: {kept} | enriched: {enriched} | movies: {movies}")
    if TMDB_KEY: print(f"  descriptions attached: {got_desc} | episode names added: {got_sub}")
    return tv

def build_m3u():
    lines = [f'#EXTM3U url-tvg="{EPG_RAW_URL}"', ""]
    disp = {v[0]: v[1] for v in WL_CHANNEL_MAP.values()}
    for local_id in WL_M3U_ORDER:
        lines.append(
            f'#EXTINF:-1 group-title="whiplash" tvg-id="{local_id}" '
            f'tvg-logo="{WL_LOGOS[local_id]}",{disp[local_id]}')
        lines.append(WL_STREAMS[local_id])
    return "\n".join(lines) + "\n"

def indent(elem, level=0):
    i = "\n" + level * "  "
    if len(elem):
        if not elem.text or not elem.text.strip(): elem.text = i + "  "
        for child in elem:
            indent(child, level + 1)
            if not child.tail or not child.tail.strip(): child.tail = i + "  "
        if not elem[-1].tail or not elem[-1].tail.strip(): elem[-1].tail = i
    else:
        if level and (not elem.tail or not elem.tail.strip()): elem.tail = i

EPG_OUTPUT = "epg.xml"
M3U_OUTPUT = "playlist.m3u"
EPG_RAW_URL = "https://raw.githubusercontent.com/s-digweed/Whiplash/main/epg.xml"

def build_all(wl_root, eel_root, cache):
    tv = ET.Element("tv", {"generator-info-name": "whiplash-eel-epg-generator"})
    add_channels(tv, WL_CHANNEL_MAP, WL_LOGOS)
    add_channels(tv, EEL_CHANNEL_MAP, EEL_LOGOS)
    print("Whiplash:"); copy_whiplash(tv, wl_root)
    print("Eel:");      build_eel(tv, eel_root, cache)
    return tv

def main():
    cache = load_desc_cache()
    if not TMDB_KEY:
        print("NOTE: TMDB_API_KEY not set - descriptions skipped this run.")
    print(f"Fetching {WL_URL} ...");  wl_root  = fetch_xml_safe(WL_URL, "Whiplash")
    print(f"Fetching {EEL_URL} ..."); eel_root = fetch_xml_safe(EEL_URL, "Eel")
    tv = build_all(wl_root, eel_root, cache)
    indent(tv)
    ET.ElementTree(tv).write(EPG_OUTPUT, encoding="UTF-8", xml_declaration=True)
    with open(M3U_OUTPUT, "w", encoding="utf-8") as f: f.write(build_m3u())
    print(f"Wrote {EPG_OUTPUT} and {M3U_OUTPUT}")
    print(f"Channels: {len(tv.findall('channel'))}, programmes: {len(tv.findall('programme'))}")

    print(f"Fetching {MIST_URL} ...")
    mist_root = fetch_mist(MIST_URL)
    if mist_root.findall("channel") or mist_root.findall("programme"):
        print("MistLive:"); mtv = build_mist(mist_root, cache)
        indent(mtv)
        ET.ElementTree(mtv).write(MIST_OUTPUT, encoding="UTF-8", xml_declaration=True)
        print(f"Wrote {MIST_OUTPUT}")
        print(f"Channels: {len(mtv.findall('channel'))}, programmes: {len(mtv.findall('programme'))}")
    else:
        print(f"MistLive feed empty/unavailable - keeping existing {MIST_OUTPUT} unchanged")

    save_desc_cache(cache)

if __name__ == "__main__":
    main()
