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
import sys
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
    # parked (not in current feed, kept in case the source drifts):
    "It's Always Sunny at": "It's Always Sunny in Philadelphia",
    "Batman Animated": "Batman: The Animated Series",
    "Superman Animated": "Superman: The Animated Series",
    "The Grim Adv. of Billy & Mandy": "The Grim Adventures of Billy & Mandy",
    "Eerie, Indiana: Other": "Eerie, Indiana: The Other Dimension",
    "Mighty Mouse '87": "Mighty Mouse: The New Adventures (1987)",
    "SRMTHFG!": "Super Robot Monkey Team Hyperforce Go!",
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
    return (RENAMES.get(base, base) + yr).strip()

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

# ── XML helpers ──
_XML_ILLEGAL = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]")
_LOCAL_IP = re.compile(r'^(https?://)?(192\.168\.|10\.|172\.(1[6-9]|2[0-9]|3[01])\.)')
HEADERS = {"User-Agent": "Mozilla/5.0 (compatible; WhiplashEPGBot/1.0)"}

def _sanitize(text): return _XML_ILLEGAL.sub("", text)

def _strip_local_images(prog):
    for tag in ("icon", "image"):
        for elem in list(prog.findall(tag)):
            src = elem.get("src") or elem.text or ""
            if _LOCAL_IP.search(src.strip()): prog.remove(elem)
    return prog

def fetch_xml(url):
    resp = requests.get(url, headers=HEADERS, timeout=30); resp.raise_for_status()
    return ET.fromstring(_sanitize(resp.content.decode("utf-8-sig", errors="replace")))

def fetch_xml_safe(url, name):
    try: return fetch_xml(url)
    except (ET.ParseError, requests.RequestException) as e:
        print(f"WARNING: {name} fetch/parse error ({e}) - skipping {name} this run")
        return ET.fromstring("<tv></tv>")

def add_channels(tv, chan_map, logos):
    for _, (local_id, display) in chan_map.items():
        if tv.find(f"./channel[@id='{local_id}']") is not None: continue
        ch = ET.SubElement(tv, "channel", {"id": local_id})
        ET.SubElement(ch, "display-name").text = display
        if local_id in logos: ET.SubElement(ch, "icon", {"src": logos[local_id]})

def copy_whiplash(tv, root):
    for src_id, (local_id, _) in WL_CHANNEL_MAP.items():
        n = 0
        for prog in root.findall("programme"):
            if prog.get("channel") != src_id: continue
            np = ET.fromstring(ET.tostring(prog)); np.set("channel", local_id)
            _strip_local_images(np); tv.append(np); n += 1
        if n: print(f"  {local_id}: {n} programmes")

def build_eel(tv, root):
    for src_id, (local_id, _) in EEL_CHANNEL_MAP.items():
        n = 0
        for prog in root.findall("programme"):
            if prog.get("channel") != src_id: continue
            raw_title = (prog.findtext("title") or "").strip()
            title, sub, season, ep, ep_end = parse_title(raw_title)
            np = ET.Element("programme", {k: prog.get(k) for k in prog.keys()})
            np.set("channel", local_id)
            ET.SubElement(np, "title", {"lang": "en"}).text = title
            if sub: ET.SubElement(np, "sub-title", {"lang": "en"}).text = sub
            if season is not None:
                onscr = f"S{season:02d}E{ep:02d}" + (f"-E{ep_end:02d}" if ep_end else "")
                ET.SubElement(np, "episode-num", {"system": "onscreen"}).text = onscr
                ET.SubElement(np, "episode-num", {"system": "xmltv_ns"}).text = f"{season-1}.{ep-1}."
            tv.append(np); n += 1
        if n: print(f"  {local_id}: {n} programmes (normalized)")

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

def build_all(wl_root, eel_root):
    tv = ET.Element("tv", {"generator-info-name": "whiplash-eel-epg-generator"})
    add_channels(tv, WL_CHANNEL_MAP, WL_LOGOS)
    add_channels(tv, EEL_CHANNEL_MAP, EEL_LOGOS)
    print("Whiplash:"); copy_whiplash(tv, wl_root)
    print("Eel:");      build_eel(tv, eel_root)
    return tv

def main():
    print(f"Fetching {WL_URL} ...");  wl_root  = fetch_xml_safe(WL_URL, "Whiplash")
    print(f"Fetching {EEL_URL} ..."); eel_root = fetch_xml_safe(EEL_URL, "Eel")
    tv = build_all(wl_root, eel_root)
    indent(tv)
    ET.ElementTree(tv).write(EPG_OUTPUT, encoding="UTF-8", xml_declaration=True)
    with open(M3U_OUTPUT, "w", encoding="utf-8") as f: f.write(build_m3u())
    print(f"Wrote {EPG_OUTPUT} and {M3U_OUTPUT}")
    print(f"Channels: {len(tv.findall('channel'))}, programmes: {len(tv.findall('programme'))}")

if __name__ == "__main__":
    main()
