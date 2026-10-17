#!/usr/bin/env python3
# Build name-keyed guide entries for Gargoyles / Dexter's Laboratory / Rocko's Modern Life
# from the attached IMDb (names+synopsis) and TMDB (Dexter segment grid) pages, plus the
# desc_cache TMDB names as spelling aliases. Output: guide_additions.json + coverage report.
import email, glob, re, html as H, json, unicodedata, difflib, collections, sys
ZIP="/tmp/claude-0/-home-claude/6492123d-aae2-5b3c-baa6-98506a8e2777/wl_zip"
WIKI_DEXTER="/root/.claude/uploads/6492123d-aae2-5b3c-baa6-98506a8e2777/c2712cfb-List_of_Dexters_Laboratory_episodes_-_Wikipedia.mht"
CACHE="/tmp/claude-0/-home-claude/6492123d-aae2-5b3c-baa6-98506a8e2777/scratchpad/wlrepo/desc_cache.json"

def extract(path):
    with open(path,'rb') as f: msg=email.message_from_binary_file(f)
    out=[]
    for part in msg.walk():
        if part.get_content_type()=="text/html":
            p=part.get_payload(decode=True)
            if p: out.append(p.decode(part.get_content_charset() or 'utf-8','replace'))
    return max(out,key=len) if out else ""
def clean(x): return H.unescape(re.sub(r'<[^>]+>','',x)).strip()

# ---- Part normalization (word & paren forms -> ": Part N") ----
WORDNUM={'one':1,'two':2,'three':3,'four':4,'five':5,'six':6,'seven':7,'eight':8,'nine':9,'ten':10}
def _wn(w):
    w=w.strip().lower()
    return WORDNUM.get(w, int(w) if w.isdigit() else None)
def norm_parts(title):
    """Standardize two-parter markers to 'Title: Part N'. Conservative: only acts on an
    explicit 'Part' keyword or a trailing '(N)'; never touches titles like 'Mock 5' / 'D2'
    / years '(1995)'. Strips any existing trailing colon so we never double it."""
    if not title: return title
    t=title.rstrip()
    def mk(base,n): return base.rstrip().rstrip(':').rstrip()+f": Part {n}"
    # "(Part One)" / "(Part 1)" at end
    m=re.search(r'\s*\(\s*Part\s+([A-Za-z]+|\d{1,2})\s*\)\s*$', t, re.I)
    if m and _wn(m.group(1)): return mk(t[:m.start()], _wn(m.group(1)))
    # "(1)" / "(2)" at end (1-2 digits -> never a 4-digit year)
    m=re.search(r'\s*\(\s*(\d{1,2})\s*\)\s*$', t)
    if m: return mk(t[:m.start()], int(m.group(1)))
    # ": Part X" or " Part X" at end (requires the word Part)
    m=re.search(r'\s*:?\s*Part\s+([A-Za-z]+|\d{1,2})\s*$', t, re.I)
    if m and _wn(m.group(1)): return mk(t[:m.start()], _wn(m.group(1)))
    return t

def _norm(s):
    s=unicodedata.normalize('NFKD',s or '')
    s=''.join(c for c in s if not unicodedata.combining(c))
    s=s.lower().replace('&','and')
    # unify all part-markers so "(1)", ": part one", " part 1" all collapse to "part1"
    s=re.sub(r'\bpart\s+(one|two|three|four|five|six|seven|eight|nine|ten)\b',
             lambda m:'part'+str(WORDNUM[m.group(1)]), s)
    s=re.sub(r'[:\-]?\s*part\s*(\d{1,2})\b', lambda m:' part'+m.group(1), s)
    s=re.sub(r'\(\s*(\d{1,2})\s*\)\s*$', lambda m:' part'+m.group(1), s.strip())
    return re.sub(r'[^a-z0-9]','',s)

# ---- IMDb parse (half-hour cards: "S{n}.E{m} <sep> TITLE" + synopsis) ----
H4=re.compile(r'<h4[^>]*>(.*?)</h4>(.*?)(?=<h4|</section|$)', re.S)
SEP=re.compile(r'^S(\d+)\.E(\d+)\s*.?\s*(.*)$')
SYN=re.compile(r'<div class="sc-[^"]*">(.*?)</div>', re.S)
def imdb(show):
    seen={}
    for f in sorted(glob.glob(ZIP+f"/{show}/*IMDb*.mht")):
        h=extract(f)
        for m in H4.finditer(h):
            mm=SEP.match(clean(m.group(1)))
            if not mm: continue
            s,e,nm=int(mm.group(1)),int(mm.group(2)),mm.group(3).strip()
            syn=""
            for sm in SYN.finditer(m.group(2)[:3500]):
                c=clean(sm.group(1))
                if len(c)>35 and 'Add a plot' not in c and 'ratingGroup' not in c: syn=c; break
            k=(s,e)
            if k not in seen or len(syn)>len(seen[k][1]): seen[k]=(nm,syn)
    return seen

# ---- TMDB Dexter per-segment grid from the season pages ----
def tmdb_dexter():
    pat=re.compile(r'data-episode-number="(\d+)"\s+data-season-number="(\d+)"[^>]*title="([^"]*)"')
    rows=set()
    for f in glob.glob(ZIP+"/Dexter's Lab/*The Movie D*.mht"):
        h=extract(f)
        for e,s,ti in pat.findall(h):
            m=re.search(r'Episode \d+ - (.*)$', ti)
            if m: rows.add((int(s),int(e),H.unescape(m.group(1))))
    return sorted(rows)

# ---- desc_cache TMDB names (aliases) ----
def cache_names(tmdbid):
    c=json.load(open(CACHE)); eps=c["episodes"]
    out={}
    for k,v in eps.items():
        if k.startswith(f"{tmdbid}|"):
            _,s,e=k.split('|'); out[(int(s),int(e))]=v.get('n','')
    return out

def split_segs(joined):
    return [p.strip() for p in joined.split('/') if p.strip()]

# ============ build per show ============
def build_segmented(show, join_syn_note=False):
    """Return eps-map: norm(segment_name) -> {title: '<hh join>', desc: '<synopsis>'}."""
    hh=imdb(show)                       # (s,e)->(joinedtitle, synopsis)
    segmap={}
    halfhours=[]
    for (s,e),(title,syn) in sorted(hh.items()):
        segs=[norm_parts(x) for x in split_segs(title)]
        disp=" / ".join(segs)
        halfhours.append((s,e,segs,disp,syn))
        for seg in segs:
            key=_norm(seg)
            if key and key not in segmap:
                segmap[key]={"title":disp,"desc":syn or None}
    return segmap, halfhours

def build_gargoyles():
    eps=imdb("Gargoyles")
    namemap={}
    for (s,e),(title,syn) in sorted(eps.items()):
        disp=norm_parts(title)
        namemap[_norm(title)]={"title":disp,"desc":syn or None}
        namemap[_norm(disp)]={"title":disp,"desc":syn or None}
    return namemap, eps

if __name__=="__main__":
    out={}
    # Gargoyles (non-segmented)
    g,geps=build_gargoyles()
    # seed TMDB-name aliases from cache (bridge spelling drift like "Goes Hollywood")
    gca=cache_names(1719)
    gmiss=[]
    # map IMDb by (s,e) too, for alias seeding by position isn't safe (numbering differs) -> match by norm name
    inv={ _norm(v["title"]):v for v in g.values() }
    for (s,e),tname in gca.items():
        if _norm(tname) in g: continue
        # fuzzy to an IMDb title
        cand=difflib.get_close_matches(_norm(tname), list(inv.keys()), n=1, cutoff=0.86)
        if cand:
            g[_norm(tname)]=inv[cand[0]]
        else:
            gmiss.append((s,e,tname))
    out["Gargoyles"]={"mode":"name","eps":g}

    # Dexter (segmented) — key by TMDB segment names (what the feed uses)
    dseg, dhh = build_segmented("Dexter's Lab")
    tg=tmdb_dexter()
    # build a lookup of IMDb half-hour by any normalized segment
    deps={}   # final keys
    dmiss=[]
    # index half-hours' segs normalized
    hh_index={}
    for s,e,segs,disp,syn in dhh:
        for seg in segs: hh_index.setdefault(_norm(seg),(disp,syn))
    allkeys=list(hh_index.keys())
    for s,e,tname in tg:
        k=_norm(tname)
        if k in hh_index:
            disp,syn=hh_index[k]; deps[k]={"title":disp,"desc":syn or None}
        else:
            cand=difflib.get_close_matches(k, allkeys, n=1, cutoff=0.84)
            if cand:
                disp,syn=hh_index[cand[0]]; deps[k]={"title":disp,"desc":syn or None}
            else:
                dmiss.append((s,e,tname))
    # also keep the raw IMDb-segment keys (covers feed names that match IMDb spelling)
    for k,v in dseg.items(): deps.setdefault(k,v)
    out["Dexter's Laboratory"]={"mode":"name","eps":deps}

    # Rocko (segmented) — no TMDB page; key by IMDb segment names + cache aliases
    rseg, rhh = build_segmented("Rocko's Modern Life")
    rca=cache_names(657)
    rmiss=[]
    rkeys=list(rseg.keys())
    for (s,e),tname in rca.items():
        if _norm(tname) in rseg: continue
        cand=difflib.get_close_matches(_norm(tname), rkeys, n=1, cutoff=0.84)
        if cand: rseg[_norm(tname)]=rseg[cand[0]]
        else: rmiss.append((s,e,tname))
    out["Rocko's Modern Life"]={"mode":"name","eps":rseg}

    json.dump(out, open("guide_additions.json","w"), ensure_ascii=False, indent=1, sort_keys=True)
    # ---- report ----
    print("Gargoyles: %d IMDb eps, %d guide keys; cache-alias misses=%d %s"%(len(geps),len(g),len(gmiss),gmiss[:6]))
    print("Dexter:    %d IMDb half-hours, %d TMDB segments, %d guide keys; TMDB->IMDb misses=%d"%(len(dhh),len(tg),len(deps),len(dmiss)))
    for m in dmiss: print("    DEX MISS",m)
    print("Rocko:     %d IMDb half-hours, %d guide keys; cache-alias misses=%d %s"%(len(rhh),len(rseg),len(rmiss),rmiss[:10]))
