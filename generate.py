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
import unicodedata
import requests
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo

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
    "C121.244.ersatztv.org": ("toon-diggity", "Toon Diggity"),  # feed moved it off C3.147 (now an orphan/stale id)
    "C122.245.ersatztv.org": ("toon-diggity", "Toon Diggity"),  # Nov 2026: feed moved it again (C121.244 kept in case it flips back)
}
EEL_LOGOS = {
    "eel-channel":  "https://i.imgur.com/YBZUFXs.png",
    "fizz":         "https://i.imgur.com/0z5rG3A.png",
    "toon-diggity": "https://i.imgur.com/GhzJMF9.png",
}
# The eel feed occasionally RENUMBERS a source channel id (e.g. Toon Diggity moved
# C3.147 -> C121.244, leaving C3.147 as a stale orphan). build_eel self-heals: if a
# configured id is gone from the feed, it re-finds the channel by its display-name
# (keyed on the stable tvg-id) and logs a NOTE. Extra display-name spellings the feed
# might use go here; the display-names in EEL_CHANNEL_MAP are matched automatically.
EEL_NAME_ALIASES = {
    "toon disney shuffle": "toon-diggity",
    "toon disney":         "toon-diggity",
    "toon disney shorts":  "toon-diggity",
    "cartoon shuffle":     "toon-diggity",   # Nov 2026 rebrand; our guide keeps "Toon Diggity"
    "e toons":             "toon-diggity",   # Nov 26 2026 rebrand ("122 E Toons"); guide keeps "Toon Diggity"
    "etoons":              "toon-diggity",
}
def _norm_chan_name(s):
    s = re.sub(r"^\s*\d+\s*", "", (s or "").strip())      # drop the feed's leading channel number
    return re.sub(r"[^a-z0-9]+", " ", s.lower()).strip()

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
ABSOLUTE_SHOWS = {"dragon ball", "dragon ball z"}   # "Dragon Ball Z 140" = ep 140, not S01 E40

# Show-name renames, keyed on the parsed base title (trailing "(YYYY)" kept)
RENAMES = {
    "Garfield": "Garfield and Friends",
    "DuckTales": "DuckTales (1987)",   # disambiguate from the 2017 reboot (feed = the original)
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
    "Homeless in Japan": "Homeless in Japan (2011)",
    "Homeless In Japan": "Homeless in Japan (2011)",
    "The State": "The State (1994)",
    "Beavis And Butt-Head": "Beavis and Butt-Head",   # disambiguate from the other series of the same name
    "Shin-Chan": "Crayon Shin-chan",
    "Chip n' Dale Rescue Rangers": "Chip 'n Dale Rescue Rangers",
    "Oban Star-Racers": "Ōban Star-Racers",
    "Snoppy's Getting Married, Charlie Brown": "Snoopy's Getting Married, Charlie Brown",  # feed typo
    # parked (not in current feed, kept in case the source drifts):
    "It's Always Sunny at": "It's Always Sunny in Philadelphia",
    "Batman Animated": "Batman: The Animated Series",
    "Superman Animated": "Superman: The Animated Series",
    "The Grim Adv. of Billy & Mandy": "The Grim Adventures of Billy & Mandy",
    "Eerie, Indiana: Other": "Eerie, Indiana: The Other Dimension",
    "Mighty Mouse '87": "Mighty Mouse: The New Adventures (1987)",
    "SRMTHFG!": "Super Robot Monkey Team Hyperforce Go!",
    # Toon Diggity (Cartoon Shuffle) feed spellings, Nov 2026
    "Mighty Mouse TNA": "Mighty Mouse: The New Adventures (1987)",
    "Oblongs": "The Oblongs",
    "FUNKY COPS": "Funky Cops",
    "Charlie Brown and Snoopy Show": "The Charlie Brown and Snoopy Show",
    "Ping Pong Club": "The Ping Pong Club",
    "Super Milk Chan USA": "The Super Milk-Chan Show",   # TMDB/Netflix name
    "Lupin The Third Part II": "Lupin the Third Part II",
    "Gay Pur-ee": "Gay Purr-ee",                          # real title (feed misspells it; TMDB match)
    "Free for All": "Free for All (2003)",                # Showtime series; year disambiguates lookups
    "1000 Ways To Die": "1000 Ways to Die",
    "D'Isigny Cartoons": "Disney Cartoons",               # Fizz feed's garbled spelling -> existing blurb
    "Tenchi Muyo! Mihoshi Special": "Tenchi Muyo!: Galaxy Police Mihoshi Space Adventure (1994)",  # feed "T107b ..."
}

# Fuzzy renames: (pattern, canonical) applied when the exact table misses.
# Catches truncated / variant titles, e.g. a bare "It's Always Sunny".
REGEX_RENAMES = [
    (re.compile(r"^Bad Religion:?\s+Live at the Palladium$", re.I),
     "Bad Religion: Live at the Palladium (2006)"),
    (re.compile(r"^Dead Kennedys:?\s+Live at (?:the )?Wust Radio Music Hall$", re.I),
     "Dead Kennedys: Live at Wust Radio Music Hall (1985)"),
    (re.compile(r"^It[\u2019']?s\s+Always\s+Sunny\b.*$", re.I),
     "It's Always Sunny in Philadelphia"),    # Toon Diggity one-off: Mickey's birthday (Nov 18) themed Afternoon Shuffle
    (re.compile(r"^Afternoon Shuffle:\s*Mickey[\u2019']?s Birthday(?: Party)?$", re.I),
     "Mickey's Birthday Party (1942)"),
]

# Fixed descriptions for block/filler programmes with no episode data (keyed by title).
_FIZZ_MIX_DESC = ("Classic cartoons like Looney Tunes, Tom and Jerry, Woody Woodpecker, "
                  "Droopy, Hubley Studio, NFB Canada and Zagreb Film animated shorts plus some "
                  "pop and rock music videos.")
_LATE_NIGHT_MIX_DESC = ("Your hand-picked midnight refill of Walt Disney Cartoon Classics, Looney Tunes, "
                        "Tom and Jerry, Woody Woodpecker, Droopy, and animated shorts from Hubley Studio, NFB Canada and "
                        "Zagreb Film, with pop and rock music videos fizzing away while the "
                        "rest of the world sleeps.")
_TOON_DISNEY_DESC = "Timeless theatrical animated shorts from Disney's golden age."
FIXED_DESC = {
    # our own write-ups (same text on CN Classic + Jpuffle5 in DyrecTV boom_enrich.py)
    "Tom and Jerry": "Tom the cat and Jerry the mouse are frenemies whose small squabbles spiral into "
                     "traps, crashes and all-out cartoon mayhem. Sometimes they team up against a common "
                     "enemy; other times one of them sides with the enemy against the other.",
    "Dexter's Laboratory": "Dexter, a boy-genius with a secret laboratory, constantly battles his sister "
                           "Dee Dee, who always gains access despite his best efforts to keep her out, as well "
                           "as his arch-rival and neighbor, Mandark.",
    "The Jetsons": "Meet George Jetson and his quirky family: wife Jane, son Elroy and daughter Judy. "
                   "Living in the automated, push-button world of the future hasn't made life any easier "
                   "for the harried husband and father, who gets into one comical misadventure after another!",
    "Classic Wrestling":  "Old-school grappling, larger-than-life legends and matches from wrestling's "
                          "golden era when every week felt like a pay-per-view.",   # Eel Channel block
    "Late Night Mix":     _LATE_NIGHT_MIX_DESC,
    "Evening Mix":        _FIZZ_MIX_DESC,
    "Toon Disney Shorts": _TOON_DISNEY_DESC,   # parked: old feed title for the block
    "Disney Cartoons":    _TOON_DISNEY_DESC,   # feed renamed "Toon Disney Cartoons/Shorts" -> "Disney Cartoons"
    "You're on Nickelodeon, Charlie Brown":
        "The animated adventures of Charlie Brown, Snoopy and the rest of the Peanuts gang.",
    "Disney Channel Original Movie":
        "A made-for-TV Disney Channel Original Movie, spanning teen comedies, musicals, fantasy and adventure.",
    "Spider-Man: The Animated Series":
        "When college student, Peter Parker, is bitten by a genetically altered spider, he "
        "gains Spider-like powers and must use his gifts to fight crime in New York City as "
        "the superhero, Spider-Man, whilst trying to have a normal personal life.",
    "AfterToon Movie":
        "An afternoon feature presentation, a family or animated film capping off the cartoon lineup.",
    "Saturday Night Movie":
        "A Saturday night feature presentation, a family film to round out the night.",
    "Sunday Night Movie":
        "A Sunday night feature presentation, a family film to close out the weekend.",
    "Cartoon Theater":
        "Feature-length animated movies, theatrical releases, and television specials "
        "distributed by Hanna-Barbera Studios, Warner Bros., Disney, 20th Century Fox, "
        "Universal, Columbia, Paramount, DreamWorks, and MGM.",
    "Adult Halloween Special":
        "The spooky stuff they aired after the kids went to bed."
        "\n\n"
        "Lights off, zero supervision.",
    "Retro Blast Halloween":
        "Enjoy classic Halloween specials and movies including Scooby-Doo, Courage the "
        "Cowardly Dog, The Simpsons, The Grim Adventures of Billy & Mandy, Hocus Pocus (1993), "
        "Halloweentown (1998), Nightmare Before Christmas (1993), and the original 1978 Halloween.",
    "Fridays Halloween":
        "Get ready for a spooky Friday night of classic chills and weird thrills. Retro Blast "
        "brings back the eeriest animation from the vault.",
    "Horror Movie":
        "Close the weekend with a scream. A classic horror movie, served late and uncut. "
        "\n\n"
        "Tune in if you dare.",
    "Saturday Late Night Movie":
        "Unwind your weekend the right way with the Saturday Late Night Movie, a nostalgic "
        "television sanctuary dedicated to the night owls, animation enthusiasts, and "
        "insomniacs. Broadcasting directly from the deep archives of the Cartoon Network and "
        "Adult Swim Universes, this retro block strips away the standard daytime schedule to "
        "showcase full-length animated features that are a little darker, a little weirder, "
        "and entirely captivating.",
    # ── Fizz blocks ──
    "Fizz Cartoons":
        "Vintage fizz from the golden age of animation: Tom and Jerry, Looney Tunes, MGM shorts, Walter Lantz "
        "Cartunes and Fleischer classics, mixed with international gems from the NFB/ONF, "
        "Zagreb Film and beyond.",
    "Fizz Vidz":
        "Three decades of rock and pop on tap, with music videos from the 80s to the 00s, "
        "fizzing you through the small hours.",
    # ── Toon Diggity (Cartoon Shuffle) shorts blocks ──
    "Secret Stash":                           # feed title kept (~5:20-6 AM ET)
        "The dark corner of the animation shelf. Magnus Carlsson's Robin, Joe Cartoon's "
        "Flash-era weirdness, trippy experiments and surreal shorts, all handpicked for the "
        "hours nobody's watching."
        "\n\n"
        "Don't tell the kids.",
    "Breakfast Shorts":                       # feed: "Morning Shuffle" (9-10 AM ET, Nov 27 2026)
        "Pour the cereal, the projector's already running."
        "\n\n"
        "Disney Cartoons, Tom and Jerry, Bugs Bunny and the Looney Tunes gang, MGM and UPA shorts, "
        "with Terrytoons, George Pal's Puppetoons and Zagreb Film rolling out of the vault."
        "\n\n"
        "Spoon in one hand, remote in the other.",
    "Technicolor Toybox":                     # feed: "Late Morning Shuffle" (~10:30 AM-noon ET)
        "The late-morning matinee, served in Technicolor."
        "\n\n"
        "Disney's timeless classics, Looney Tunes in full Merrie Melodies swing and Puppetoons "
        "built one carved figure at a time, all shuffled in with Woody Woodpecker, Droopy and "
        "whatever else tumbles out."
        "\n\n"
        "Everything back in the box by noon.",
    # ── Toon Diggity (eToons) studio segments, Nov 26 2026 grid ──
    "Terrytoons":                             # feed: "Terry Toons" (~6 AM ET)
        "Sign-on, straight out of New Rochelle."
        "\n\n"
        "Paul Terry's barnyard opens the day: Farmer Al Falfa, Gandy Goose and Sourpuss, Kiko the "
        "Kangaroo, Puddy the Pup, those magpie troublemakers Heckle and Jeckle, and a pint-sized "
        "Mighty Mouse flying in before the coffee's done."
        "\n\n"
        "First reel of the morning.",
    "Columbia Cavalcade":                     # ~6:30 AM ET
        "Columbia's cartoon cabinet swings open."
        "\n\n"
        "Charles Mintz's Krazy Kat and Scrappy, the Technicolor Color Rhapsodies, The Fox and the "
        "Crow trading wisecracks, and UPA's Jolly Frolics with Gerald McBoing-Boing and a nearsighted "
        "Mr. Magoo squinting his way through it all."
        "\n\n"
        "The lady with the torch says good morning.",
    "Universal Union":                        # ~7 AM ET
        "Rise and peck."
        "\n\n"
        "Woody Woodpecker leads the morning crew with Andy Panda, Chilly Willy, Homer Pigeon, "
        "Inspector Willoughby and Oswald the Lucky Rabbit, plus Cartune Classics and Oscar-nominated "
        "shorts from the Lantz studio."
        "\n\n"
        "The union never strikes.",
    "Paramount Potluck":                      # ~8 AM ET
        "Paramount's cooking!"
        "\n\n"
        "Felix the Cat from the silent days, Fleischer's Koko the Clown, Betty Boop, Popeye and "
        "Superman, Famous Studios' Casper, Little Audrey, Little Lulu, Baby Huey and Herman and "
        "Katnip, plus George Pal's Puppetoons."
        "\n\n"
        "Come hungry, leave laughing.",
    "MGM Gems":                               # ~12:10 PM ET
        "Lunch break at the studio with the roaring lion."
        "\n\n"
        "Hanna and Barbera's Tom and Jerry, Tex Avery's Droopy and Screwy Squirrel, Barney Bear, "
        "Spike and Tyke, George and Junior, The Captain and the Kids, plus Harman-Ising's Happy "
        "Harmonies and Bosko, and Ub Iwerks' Flip the Frog and Willie Whopper."
        "\n\n"
        "Gems, every one.",
    "Merrie Melodies Matinee":                # feed: "Looney Tunes" (~1:10 PM ET)
        "One hour of the funniest cartoons ever made. Argue with us later."
        "\n\n"
        "Bugs Bunny, Daffy Duck, Porky Pig, Elmer Fudd, Sylvester, Tweety, Yosemite Sam, Speedy "
        "Gonzales, Marvin the Martian, the Tasmanian Devil, and the Road Runner leaving Wile E. "
        "Coyote in the dust."
        "\n\n"
        "Beep beep.",
    "A Charlie Brown Thanksgiving (1973)":    # IMDb synopsis (in case the feed sends it)
        "Peppermint Patty invites herself and her friends over to Charlie Brown's for Thanksgiving, "
        "and with Linus, Snoopy, and Woodstock, he attempts to throw together a Thanksgiving dinner.",
    "Tenchi Muyo!: Galaxy Police Mihoshi Space Adventure (1994)":
        "A side story about Mihoshi's life as a Galaxy Police Officer. Mihoshi introduces her partner, "
        "Kiyone, an up-and-coming officer who believes that having Mihoshi as her partner could be the "
        "end of her career, and explains how they solved the case of the Missing Super Energy.",
    "Starcade":                               # Taqi's text; show-level only (no sub-title, no S/E)
        "Contestants answer questions about video games and then play featured arcade games in order "
        "to earn enough points to beat the opponents.",
    "Looney Tunes":                           # Fizz late-night block (~11:05 PM ET); Toon Diggity's is renamed
        "A fizzy nightcap from the Warner Bros. cellar."
        "\n\n"
        "Starring Bugs Bunny, Daffy Duck, Porky Pig, Elmer Fudd, Yosemite Sam, Sylvester and Tweety, "
        "Foghorn Leghorn, Wile E. Coyote and the Road Runner in full Technicolor chaos."
        "\n\n"
        "Stay up, it's worth it.",
    "Afternoon Shuffle":
        "An after-school reel of theatrical shorts: Tom and Jerry, Looney Tunes, Tex Avery, Walter Lantz "
        "Cartunes and Fleischer classics, cut with international gems from NFB/ONF Canada and Zagreb Film."
        "\n\n"
        "Homework can wait.",
    # ── one-off specials ──
    "Bad Religion: Live at the Palladium (2006)":
        "Live at the Palladium is a live concert DVD by the punk band Bad Religion, released in "
        "March 2006. It features footage from two nights at the Palladium in Hollywood, "
        "California, on November 21 and 22, 2004.",
    "Dead Kennedys: Live at Wust Radio Music Hall (1985)":
        "Dead Kennedys perform live at Wust Radio Music Hall in Washington, D.C., on November 18, "
        "1985. Lead singer Jello Biafra delivers a politically charged speech criticizing 'phony "
        "patriotic pigs' and 'Nazi rednecks' before the band begins a high-energy punk rock "
        "performance.",
    "Mickey's Birthday Party (1942)":         # feed: "Afternoon Shuffle: Mickey's Birthday"
        "The gang throws Mickey a surprise birthday party; his present is an electric organ, which "
        "Minnie plays while Mickey does a jazzy dance. Goofy bakes the cake, but keeps having trouble "
        "with it falling. The gang does a conga line to a Latin tune.",
    # ── Toon Diggity films (feed: "Lupin III" + sub-title film; joined to one title) ──
    "Lupin III: The Legend of the Gold of Babylon (1985)":
        "In New York, ancient tablets point to the lost gold of Babylon. Lupin races two rival crime "
        "families, Zenigata's new all-female police squad and a mysterious old woman named Rosetta to "
        "find the treasure, while Halley's Comet holds the key to its secret.",
    "Lupin III: The Fuma Conspiracy (1987)":
        "Goemon's wedding to Murasaki is crashed by the Fuma ninja clan, who kidnap the bride and "
        "demand her family's ancient treasure as ransom. Lupin, Jigen and Fujiko join Goemon to rescue "
        "her and beat the Fuma to the treasure, with Zenigata hot on their trail.",
    # ── shows the metadata lookups can't describe ──
    "Homeless in Japan (2011)":
        "From camping out in the park, to capsule hotels and cyber cafes, we dive into the weird "
        "and wonderful world of the homeless in Japan.",
    "Crapston Villas":                        # Channel 4 show blurb (fallback for unlisted episodes)
        "This animated soap opens up the glamorous world of Crapston Villas. We see the hilarious antics "
        "of the inhabitants of this much sought-after residential property.",
    "Crayon Shin-chan":                       # fallback for episodes not in fizz_guide.json (Vitello dub)
        "Five-year-old Shinnosuke \"Shin-chan\" Nohara turns everyday life in Kasukabe, Japan, into chaos. "
        "Armed with blunt remarks, absurd logic and endless cheek, he drives his parents, teachers and "
        "neighbors up the wall, but there's always room for a warm moment with his family and friends.",
    "Nickelodeon GUTS":                       # IMDb show blurb
        "Three kids donning the different colors blue, red, and purple compete in relatively "
        "cool-looking olympic-style games to achieve as many points as they can.",
    "Homeless in Denton":
        "A local documentary-style comedy series that follows two \"homeless\" guys wandering "
        "around Denton, Texas.",
    "Dude, What Would Happen":                # fallback for episodes not in fizz_guide.json
        "Three teens, C.J., Jackson and Ali, wonder what would happen if some wild event, scheme "
        "or experiment were to occur, then set out to create it themselves, consulting experts "
        "when needed.",
    # ── Eel Channel blocks (blank lines between paragraphs render as line breaks) ──
    "The Late Shift":
        "The office's shuttered, the takeout's gone cold, and the tubes are still warm. "
        "The Late Shift is the Eel Channel after dark."
        "\n\n"
        "Insomniac cartoons, vintage grapplers, music videos warped off a third-gen tape, "
        "and static-soaked oddities out of the archive at 4 AM, all buzzing at a cozy 502p."
        "\n\n"
        "Don't adjust your set; that hum is on purpose.",
    "The Break Room":
        "Your midday jolt, no talk, no ads."
        "\n\n"
        "Back-to-back music videos: fresh, forgotten, and gloriously scuffed — enough to "
        "carry you clean through to clock-out."
        "\n\n"
        "Pull up a folding chair.",
    "The Desk Jockey":                      # feed: "Morning Videos" (~11 AM)
        "Badge on, inbox filling, the copier warming up somewhere down the hall."
        "\n\n"
        "A wake-up reel of music videos: chart hits, cult cuts and VHS-worn favorites you "
        "swore you'd forgotten."
        "\n\n"
        "Look busy.",
    "Nightwave":                              # retired Nov 2026 (no late-night video block); kept for reuse
        "Half past eleven and the signal goes molten."
        "\n\n"
        "A neon loop of music videos: new drops, deep cuts, and signal-bent classics bleeding "
        "one into the next, strobing through the dark like a jukebox nobody can unplug."
        "\n\n"
        "Lights low, voltage high.",
}

# Eel Channel segment renames that the title-only RENAMES table can't express.
#  - "Music Videos" airs twice under one feed title: a ~1 PM afternoon block and a
#    ~11:25-11:30 PM late-night block (2x/week). Split them by local start hour.
# ("The Late Shift" keeps its feed title; its description is handled via FIXED_DESC.)
# Feed start attr looks like "20260927131000 -0400"; digits [8:10] are the local hour.
# Some Eel-feed titles arrive in BLOCK CAPITALS ("CRAPSTON VILLAS", "RENO 911!").
# Title-case them so they match the guide, renames and the rest of the grid.
_KEEP_CAPS = {"TV", "MTV", "USA", "UK", "US", "NYPD", "CSI", "SNL", "UFO", "BBC", "ITV", "ABC", "NBC",
              "CBS", "WWE", "WWF", "DC", "II", "III", "IV", "VI", "VII", "VIII", "IX", "XL", "AM", "PM", "DJ",
              "FLCL"}
_SMALL = {"a", "an", "and", "the", "of", "in", "on", "at", "to", "for", "or", "but", "nor", "vs", "vs.", "by", "with"}
def _decap(title):
    letters = re.sub(r"[^A-Za-z]", "", title or "")
    if len(letters) < 4 or letters != letters.upper():
        return title                                   # not shouting -> leave alone
    words = title.split(" "); out = []
    for i, w in enumerate(words):
        core = re.sub(r"[^A-Za-z0-9']", "", w)
        stem = re.sub(r"'S$", "", core.upper()).replace("'", "")
        if stem in _KEEP_CAPS or re.search(r"\d", core):
            out.append(re.sub(r"'S\b", "'s", w)); continue     # MTV'S -> MTV's
        lw = w.lower()
        if 0 < i < len(words) - 1 and lw in _SMALL:
            out.append(lw); continue
        # capitalise each hyphen/slash part: SPIDER-MAN -> Spider-Man; IT'S -> It's
        out.append(re.sub(r"[A-Za-z]+(?:'[A-Za-z]+)?", lambda m: m.group(0)[0].upper() + m.group(0)[1:].lower(), lw))
    return " ".join(out)

def _eel_segment_rename(title, start, channel=None):
    # Fizz's nightly classic-shorts block is titled just "Cartoons" in the feed.
    if channel == "fizz" and title == "Cartoons":
        return "Fizz Cartoons"
    # Nov 2026 grid: Eel's video blocks got their own feed titles.
    if title == "Morning Videos":
        return "The Desk Jockey"
    if title == "Afternoon Videos":
        return "The Break Room"
    # Nov 13 2026 grid: Toon Diggity split its morning shorts into two blocks.
    if channel == "toon-diggity" and title in ("Early Morning Shuffle", "Morning Shuffle"):
        return "Breakfast Shorts"
    if channel == "toon-diggity" and title == "Late Morning Shuffle":
        return "Technicolor Toybox"
    # Nov 26 2026 eToons grid: studio segments (blurbs in FIXED_DESC).
    if channel == "toon-diggity" and title == "Terry Toons":
        return "Terrytoons"
    if channel == "toon-diggity" and title == "Looney Tunes":
        return "Merrie Melodies Matinee"
    if title == "Music Videos":
        try:
            hr = int((start or "")[8:10])
        except ValueError:
            hr = 13                      # unparsable -> treat as the afternoon block
        return "The Break Room" if 10 <= hr < 18 else "Nightwave"
    return title

# Renamed titles that should NOT carry the source's trailing (YYYY)
DROP_YEAR = {"Batman: The Animated Series"}

# Feed "T<series><ep>" codes read as season+episode ("T225 Tenchi Universe" -> S02 E25), but the
# leading digit is the FRANCHISE series (Tenchi Universe = Tenchi's 2nd TV series, 26 eps, one
# season). Remap that season per show: {show: {feed_season: real_season}}.
SEASON_REMAP = {
    "Tenchi Universe": {2: 1},
}

# ── Tenchi Universe (Wikipedia list of episodes) ─────────────────────────────
# The feed codes it "T2NN Tenchi Universe" (franchise series 2, episode NN = absolute 1-26).
# Shown per arc, as Taqi wants: "Tenchi Universe - <Arc>" + episode name; ONE season (S01 E01-E26),
#   only the arc in the title changes: 1-10 Earth Adventure, 11-13 Time and Space Adventures, 14-26 Space Adventure.
# Names + synopses straight from Wikipedia; no metadata lookups for this show.
TENCHI_UNIVERSE = [  # index = absolute episode - 1: (arc, season, episode, name, synopsis)
    ('Earth Adventure', 1, 1, 'No Need for Discussions!',
     'Pursued by Galaxy Police Detective Mihoshi, Ryoko crash lands on Earth and interjects herself into the lives of the Masaki family, particularly the teenage son Tenchi.'),
    ('Earth Adventure', 1, 2, 'No Need for a Princess!',
     'Mihoshi activates a distress signal, to which Princess Ayeka responds. Rivalries between Ryoko and Ayeka ignite and all wind up stuck on Earth.'),
    ('Earth Adventure', 1, 3, 'No Need for Worries!',
     'Sasami goes in search of her older sister Ayeka and is caught up in the growing and conflicting household.'),
    ('Earth Adventure', 1, 4, 'No Need for Monsters!',
     'During local festivities, Ryoko becomes fascinated with the legend about a monster entombed in a cave shrine. Conflicts with Ayeka ensue and the monster is revealed to be Washu, a mad scientist.'),
    ('Earth Adventure', 1, 5, 'No Need for Partners!',
     'Kiyone gleefully celebrates the "passing" of her mismatched partner Mihoshi until superiors ask her to investigate the possibility that Mihoshi might be alive on the isolated planet Earth.'),
    ('Earth Adventure', 1, 6, 'No Need for Resident Officers!',
     "Mihoshi and Kiyone are reassigned to Earth, much to Kiyone's chagrin. Having to adjust to the high cost of living, both take a series of part-time jobs while still being on-call for galaxy police emergencies."),
    ('Earth Adventure', 1, 7, 'No Need for a Carnival!',
     'The extraterrestrial group participates at all levels when festivities are held at the Masaki Shrine.'),
    ('Earth Adventure', 1, 8, 'No Need for a Genius!',
     'Washu is determined to get back in the game with a series of inventions, starting with a mecha clone of herself; plans go awry when Mihoshi gets involved.'),
    ('Earth Adventure', 1, 9, 'No Need for Memories!',
     "A winter snowfall elicits various responses from the household, culminating in the annual observation of the death of Tenchi's mother."),
    ('Earth Adventure', 1, 10, 'No Need for an Arch Rival!',
     'Bounty hunter Nagi catches up with Ryoko and kidnaps Tenchi to lure her away from the safety of the group.'),
    ('Time and Space Adventures', 1, 11, 'Time and Space Adventures: Part 1',
     "Washu invents a machine capable of generating alternative realities to the specifics of the user. Curious and competing members of the extraterrestrial group overwhelm the machine and disappear into the new realities. In the First Part, the group participates in Ayeka's world in Heian period Japan where she and Tenchi are arranged to be married only after he defeats the Rashomon who is Ryoko."),
    ('Time and Space Adventures', 1, 12, 'Time and Space Adventures: Part 2',
     "Washu continues repairs and attempts to bring them back by eliminating worlds one at a time. In the second part, Kiyone imagines life as a drifter in a local inn after an abrupt career change. In Sasami's world, she becomes a magical girl heroine who interjects herself in the high school love triangle of Ayeka, Tenchi, and Ryoko."),
    ('Time and Space Adventures', 1, 13, 'Time and Space Adventures: Part 3',
     "Repairs and rescue by Washu are almost complete. In Mihoshi's world, she is a housewife married to Tenchi, while Ayeka and Ryoko are her critical sister-in-law and flirting neighbor, respectively. In Ryoko's world, Tenchi and she are Bonnie and Clyde characters on the run from FBI Agents Kiyone and Mihoshi."),
    ('Space Adventure', 1, 14, 'No Need for a Rebellion!',
     'Incredible events within the Jurai monarchy result in the arrest of Princess Ayeka, Sasami, and Ryoko by royal guards and Kiyone and Mihoshi are recalled to Galaxy Police headquarters. The Masaki family, Washu, and Ryo-ohki launch a rescue mission.'),
    ('Space Adventure', 1, 15, 'No Need for an Escape!',
     'The Masaki family, Washu, and now Mihoshi and Kiyone help the captives escape from Galaxy Police Headquarters.'),
    ('Space Adventure', 1, 16, 'No Need for Hiding!',
     'Determined to get to Jurai and low on resources, the group opens a bar with themselves as bartenders and hostesses. Nagi drops in determined to capture Ryoko.'),
    ('Space Adventure', 1, 17, 'No Need for Hunger!',
     'A combination of engine troubles and low supplies strands the group without any food. Ryoko takes last of the cash on hand and vows to return with food.'),
    ('Space Adventure', 1, 18, 'No Need for a Ghost!',
     "The group's space ship inexplicably breaks down in an unusual area of space. After encountering an abandoned passenger ship, Sasami disappears following an ethereal young girl."),
    ('Space Adventure', 1, 19, 'No Need for Runaways!',
     "The group's space ship is hijacked by juvenile delinquents during a rest stop."),
    ('Space Adventure', 1, 20, 'No Need for Swimsuits!',
     "Again low on cash, the group sets up a snack shop and takes part-time jobs on a beach resort. Rivalries ignite again during a swimsuit competition and are further exacerbated by Nagi's participation."),
    ('Space Adventure', 1, 21, 'No Need for a Checkpoint!',
     'To get to Jurai, the group attempt to cross a necessary checkpoint disguised as members of a school field trip.'),
    ('Space Adventure', 1, 22, 'No Need for Knights!',
     "The group inadvertently crash lands on a mysterious property within the Jurai galaxy at Grandfather Katsuhito's request. Such esoteric knowledge becomes a revelation about the Masaki family and grandfather enlists the help of fabled knights to restore the monarchy."),
    ('Space Adventure', 1, 23, 'No Need for Karma!',
     "Katsuhito recounts the enmity between himself and Kagato, who is trying to usurp Katsuhito's legitimate position within the Jurai monarchy. They confront one another and Ayeka is kidnapped."),
    ('Space Adventure', 1, 24, 'No Need for Ryoko!',
     'Motivated to rescue Ayeka and stop Kagato, the group initiates an assault on the Jurai Palace. Ryoko takes the lead in a diversionary plan against Jurai forces.'),
    ('Space Adventure', 1, 25, 'No Need for a Showdown!',
     'Tenchi and the fabled knights battle their way to the throne room, culminating in a face-off between Kagato and himself.'),
    ('Space Adventure', 1, 26, 'No Need for a Conclusion!',
     'In an epilogue, Tenchi discusses the fate of most of the group, all of whom have their reputations restored or rewarded. Despite such acknowledgements, all become fond of their experience on Earth and return to the Masaki household.'),
]

# ── Storm Hawks (Toonami Wiki: names + synopses for all 52; "(Part N)" -> ": Part N") ──
STORM_HAWKS = [  # index = absolute episode - 1 (feed: "Storm Hawks 47" = S02 E21): (season, ep, name, desc)
    (1, 1, 'Age of Heroes: Part 1', 'Young Sky Knight Aerrow and his squadron, the Storm Hawks, get their first taste of battle when the sinister Master Cyclonis sends the dread Dark Ace to steal the most powerful crystal in the Atmos: the Aurora Stone.'),
    (1, 2, 'Age of Heroes: Part 2', 'Having lost the Aurora Stone to the cunning Dark Ace, The Storm Hawks mount a daring mission, sneaking into the very heart of the evil empire of Cyclonia to take the powerful crystal back.'),
    (1, 3, 'Gale Force Winds', "The Storm Hawks promise an old Sky Knight they'll rescue his granddaughter Dove, a prisoner in the clutches of Cyclonia. But when they sneak inside the Smelters of Terra Gale for the mission, they find Dove is anything but a damsel in distress."),
    (1, 4, 'The Code', 'Competing against the strict and proper Rex Guardians for a powerful Phoenix Crystal, the Storm Hawks set out to prove that old-fashioned rules belong in the history books – not in the skies of battle. to take the powerful crystal back.'),
    (1, 5, 'Tranquility Now', "Finn’s accidentally lost Junko's prized Knuckle Busters! Junko’s just not the same without them, which means Finn better find a replacement, and quick, or the Storm Hawks’ mission to stop Ravess and Snipe is doomed."),
    (1, 6, 'Best Friends Forever', 'Piper becomes fast friends with an alluring stranger named Lark, but as the Storm Hawks soon find out, there is more to their guest than meets the eye. When Piper uncovers the true identify of her new best friend, she finds herself in the battle of a lifetime.'),
    (1, 7, 'The Black Gorge', 'The Storm Hawks are stranded in the dreaded Black Gorge, from which no airship has ever returned. Now the only one who can lead them through the unspeakable dangers to recharge their power crystal is Stork!'),
    (1, 8, 'Absolute Power', "While Aerrow goes off on a super-secret mission with Starling, Finn is left in charge of the Condor. Now it's tough to tell who's in more danger, Aerrow and Starling against Repton and his Raptors, or the rest of the team with a power-mad Finn calling the shots."),
    (1, 9, 'Velocity', 'Every year dozens of Sky Knights go head to head in a treacherous bike race across Terra Saharr, competing to win a rare and powerful Velocity amulet. The adrenaline-fuelled run should give Aerrow a chance to show his stuff, but all bets are off when a mysterious masked rider shows up and plays by his own rules.'),
    (1, 10, 'Fire and Ice', 'Repton and his cronies decide to heat things up on the icy Terra Blizzaris. But even working together with the wild and crazy Absolute Zeroes, the Storm Hawks may be headed for a meltdown.'),
    (1, 11, 'King For a Day', "Finn is declared the long lost hero of Terra Vapos. Naturally he's loving every minute of it. But when he's expected to actually save them from a sinister foe, Finn learns being the Chosen One isn't all it's cracked up to be."),
    (1, 12, 'Terra Deep', "Jagged rocks and thick clouds surround them, villainous Murk Raiders are on their tail and an entire Cyclonian fleet waits for them beyond. The Storm Hawks have to fly silent and fly quick if they're going to survive Terra Deep."),
    (1, 13, 'Storm Warning', "Piper pretends to quit the team to teach the boys a lesson, but it's going to take everyone working together to stop Ravess and her dangerous plan to shut down the Storm Hawks for good."),
    (1, 14, 'A Little Trouble', "Everyone's worried when Junko agrees to look after a baby Wallop for the day. But when the Storm Hawks set out on a mission to bring construction on Snipe's new mega-ship to a standstill, what starts as a simple favor turns out to be an adventure in babysitting… of giant proportions!"),
    (1, 15, 'Thunder Run', "It's a race against the clock for the Storm Hawks! If they can't bring back a mysterious treasure from the other end of Atmos by sundown, a gangster known as The Colonel is going to have Junko for lunch! To give the Condor an extra burst of speed, Finn nabs a Velocity crystal off of a couple of Raptors. But will it be enough now that Repton's on their tail too?"),
    (1, 16, 'Escape', 'Aerrow and Radarr make a break from the escape-proof prison on Terra Zartacla. With jail warden Mr. Moss on their tail, our two heroes set out to prove anything’s possible when you’re a Storm Hawk! Using every trick in the book, the two try to outsmart their jailers and survive the dangerous jungle. But will it be enough to get them to freedom?'),
    (1, 17, 'Forbidden City', 'A double-crossing explorer has found a way inside the ancient Forbidden City, which means Snipe will get his hands on the treasure, unless the Storm Hawks can get there first. Of course they’ll have to brave a lot of dangerous traps and confusing riddles on the way in. The test is on: is Stork really prepared for anything?'),
    (1, 18, 'Leviathan', 'The Condor has been swallowed whole by a giant sky creature, with Radarr inside! The terrified locals are no help at all, so the Storm Hawks will have to set out with nothing but their skimmers and their brains to hunt down the monster, and save their ship and their friend.'),
    (1, 19, 'InFinnity', 'One Finn is plenty, but an entire Condor-full? That’s what happens when Finn accidentally sets off a crystal that creates dozens of brand new Finns, each one exactly like the next. But when Snipe gets his hands on it, the Storm Hawks quickly put those Finns to work against a growing army of Snipes!'),
    (1, 20, 'Terra Neon', 'The Storm Hawks are sharing the spotlight on glitzy Terra Neon – but not by choice. Two evil producers have taken the Terra captive and are forcing everyone to audition for their next big show. And unless they can find a star, it’s curtains!'),
    (1, 21, 'The Storm Hawks Seven', 'Starling joins the Storm Hawks for a daring mission to take back a tiny terra from the Cyclonians. Though it may seem like a harmless chunk of rock, Ravess is using the terra to house her evil sonic blaster, big enough to take out an entire airship! Unless Starling and the Hawks can find a way to work together, Ravess is going to control the skies!'),
    (1, 22, 'Talon Academy', 'Being a Cyclonian isn’t as cool as they make it sound – and Aerrow, Radarr and Piper are determined to prove that to the kids at a Talon training academy. Sneaking inside as students, the Hawks quickly turn the training ground into a battle ground and overthrow the staff. Now they’ve got to teach headmaster Snipe a lesson!'),
    (1, 23, "Siren's Song", "Trapped in The Great Expanse, the Storm Hawks face a new foe: a mysterious Sky Siren and her dangerous power – she can make them see whatever she wants them to. They'll have to outsmart her if they want to escape a giant sucking whirlpool, and that means resisting the things they each want the very most."),
    (1, 24, 'Calling All Domos', 'There’s trouble again on Terra Vapos, and since Finn saved them once before, he’s called back to Domo duty. But with the rest of the Hawks dealing with Junko’s wallop-sized toothache, Finn only has Stork to back him up. But will that be enough against the scary pirates known as The Murk Raiders?'),
    (1, 25, 'The Lesson', 'The Talons have somehow become supercharged, and unless an unusual sky-fu master can whip the Storm Hawks into shape, they’re looking at a major defeat. Only question is, are any of these strange lessons helping?'),
    (1, 26, "Dude, Where's My Condor?", 'On a whim, the Storm Hawks trade in the Condor. But by the time they realize their mistake, their beloved ship has a new owner: a frightening gangster known as The Colonel! Aerrow and the Hawks have got to get it back! But they’d better hurry – the Condor will never survive what the Colonel has planned!'),
    (2, 1, 'The Masked Masher', 'To get inside Cyclonia during its “Ultimate Warrior Championships,” the Storm Hawks enter Junko as one of the colorful competitors. Things quickly get out of hand – especially when Junko gets a little too much into character.'),
    (2, 2, "Atmos' Most Wanted", 'Thieves are on the loose, and all clues seem to point to the Storm Hawks as the culprits! Clearing your good name isn’t easy when you’re Atmos’ most wanted!'),
    (2, 3, 'Stratosphere', 'The space race is on, and Cyclonia has a head start. After discovering Ravess is commanding a battle platform high in the Stratosphere, the Storm Hawks must go higher, faster and farther than ever before to stop her.'),
    (2, 4, 'The Last Stand', 'Stuck in the unforgiving Wastelands, the Storm Hawks must fend off an old Cyclonian rival bent on revenge. Meanwhile, Junko hopes to impress the tough as nails Wallop miners they went there to rescue.'),
    (2, 5, 'Life with Lugey', 'Stork and Leugey get stuck together when Stork swallows a Gravatron Crystal. Now the Storm Hawks must find a way to get the two unstuck without Repton finding out.'),
    (2, 6, 'What Got Into Finn?', "The Storm Hawks have to deliver a weird container and are told not to open it, but Finn's curiosity gets the better of him and he opens the container, which shoots out a weird gas that turns Finn into a monster. Stork creates a cure, but gets a little carried away trying to get Finn to take it."),
    (2, 7, 'Royal Twist', "Piper meets a princess who looks exactly like her. The princess wants some adventure in her life, so she switches places with Piper and joins the Storm Hawks. Meanwhile, Piper gets into trouble when the princess' kingdom is invaded by a group of creatures known as the Nightcrawlers."),
    (2, 8, 'Second Chances', "Carver, the former Sky Knight, claims that he has reformed and wants to join the Storm Hawks. The Storm Hawks really believe that Carver has changed, except for Aerrow, who thinks that Carver hasn't changed one bit."),
    (2, 9, 'Radarr Love', 'While on a trip to Terra Neon, the Storm Hawks accidentally leave Radarr at a rest stop. Now Radarr must find a way to get back to the Condor while avoiding Cyclonians and a chicken that has a crush on him.'),
    (2, 10, "Scout's Honor", 'As part of volunteer work, Stork takes a group of young Merb scouts on a camping trip. However things go totally wrong when Stork and the scouts land on the wrong terra, which is full of vicious creatures. They also have a run in with Snipe, who is testing a new weapon of his.'),
    (2, 11, "Sky's End", "The Storm Hawks end up at Sky's End, an uncharted part of Atmos which is believed to be home to dragons. They meet a group of young dragons and try to protect them from the Murk Raiders who want to slay them."),
    (2, 12, 'Five Days', 'After winding up in a body cast, Aerrow must spend five days in bed while his wounds heal. This proves to be difficult when Master Cyclonis invades the Condor.'),
    (2, 13, 'Energy Crisis', "The Dark Ace stumbles upon a powerful suit of armor that is powered by crystals. He goes on a power hungry rampage, sucking up every crystal he can find and it's up to the Storm Hawks to stop him."),
    (2, 14, 'Dark Waters', "The Storm Hawks head to Terra Aquanos to rescue the Neck Deeps who are trapped underwater. While looking for them, the Strom Hawks are attacked by a bunch of unknown sea monsters and must find a way to get rid of them before they become the monsters' next meal."),
    (2, 15, 'Number One Fan', 'The Storm Hawks meet a young kid named Noob who claims to be their biggest fan. He asks for a tour of the Condor and the Storm Hawks agree, thinking nothing can go wrong. That is until Noob causes a lot of trouble for them and they try to get rid of him without hurting his feelings.'),
    (2, 16, 'A Colonel of Truth', 'As part of the gangster code, the Colonel becomes the Storm Hawks servant after they save his pet. The Storm Hawks make him do a bunch of nice things like do community service and give away some of his money to poor people.'),
    (2, 17, 'Shipwrecked', 'The Storm Hawks get stranded on Terra Tropika due to a giant tidal wave and try to figure out how to survive on the island. Meanwhile, Stork has to deal with a group of natives who want to make a meal out of him and think that the Condor is their god.'),
    (2, 18, 'Power Grab', "While Master Cyclonis is off on a mission, Ravess is put in charge of Cyclonia. But Ravess lets all the power go to her head which angers Snipe, who declares mutiny on his sister and becomes the new person in charge. However he also becomes power hungry and orders everyone to shoot anything that comes near Cyclonia. However, the Raptors fly close by and aren't happy getting shot at."),
    (2, 19, 'Home Movie Night', 'The Storm Hawks gather together to spend a night in the Condor watching their home movies. Each of the Storm Hawks members get a chance to show a video about themselves.'),
    (2, 20, 'Origins', 'This episode serves as a prequel to the series. In this special flashback episode, we are shown what Aerrow and his friends were like before they became the Storm Hawks.'),
    (2, 21, 'The Ultra Dudes', 'While on a Western-style terra, Finn scares away a bandit and becomes the new hero of the town. He even creates his own squad known as the Ultra Dudes, which might come in handy when the bandit returns with his own squad, the Murk Raiders. Meanwhile, the other Storm Hawks learn more about the gate that Master Cyclonis is looking for.'),
    (2, 22, 'A Wallop for All Season', "Junko goes back to his home terra to find out that the chief has decided to sign a treaty with the Cyclonians. When he can't convince the chief that the Cyclonians are evil, Junko challenges the chief to a battle to try and reason with him."),
    (2, 23, 'Payback', "The Storm Hawks are scattered all around Atmos after Repton destroys the Condor. Aerrow meets up with Arygyn and the three guardians; Finn lands on a garbage truck owned by the Blizzarians; Piper ends up on Gundstaff's terra, who helps her get back to her friends; and Junko meets a group of wrestlers who help him fight a bunch of Cyclonians. Finally, Stork goes after Repton to make him pay for destroying the Condor."),
    (2, 24, 'The Key', 'While reconstruction of the Condor gets underway with countless volunteers, Aerrow and Piper try to stop Master Cyclonis and the Dark Ace from finding the oracle stone which is the key to opening the far side door.'),
    (2, 25, 'Cyclonia Rising: Part 1', 'Master Cyclonis arms her Nightcrawlers with new crystal technology from the far side and plans to take over Atmos. Meanwhile, Piper has trouble with her new binding power and fears that if she uses it too much, it will make her evil.'),
    (2, 26, 'Cyclonia Rising: Part 2', 'In only 6 weeks, Master Cyclonis has taken over all of Atmos and has captured all of the Sky Knights. Only the Storm Hawks remain and they must find a way to stop Master Cyclonis once and for all.'),
]

# ── 1000 Ways to Die (Wikipedia: episode title + summary, matched by title; S/E stays the feed's) ──
WAYS_TO_DIE_1000 = {  # _guide_norm(title) -> (Wikipedia title, Wikipedia summary)
    'lifewillkillyou': ('Life Will Kill You', "A gun enthusiast meets his end with a rattlesnake; a young woman's sex life ends prematurely; and a bug collector suffers a fatal bite from a black widow."),
    'hardliveseasydeaths': ('Hard Lives, Easy Deaths', "A meat packer impregnates his employer's granddaughter and later meets his end in a mysteriously locked freezer; three friends learn the perils of scuba diving and flying on the same day; two brothers feud over land until one seeks revenge through a witch doctor's poison, only to fall victim himself; and a man wearing a homemade merman costume attempts to swim with fish but drowns instead."),
    'deathovereasy': ('Death Over Easy', "A smoker gets burned; a beautiful dreamer can't wake up; an inmate is caught in a deadly wire; costumed freaks go wild; a pool shark bites off more than he can swallow; and a peeping pervert finds himself in the ultimate night shack."),
    'unforcederrors': ('Unforced Errors', "A lawyer falls; a wood chipper develops a taste for manly appetites; two reckless co-eds find life a gas; a Texan's alluring wife gives him an itchy surprise; a sword swallower ends up choking on his own act; and a sex addict decides to go organic."),
    'deadanddeader': ('Dead and Deader', 'A junkie addicted to pain; a man who prefers women to toilets; a gun lover who learns the hard way; a drinker who lets the liquor hit his liver; a javelin enthusiast who gets skewered; and a man who gets rubbered out.'),
    'deathgetsbusy': ('Death Gets Busy', 'A man with anger issues meets his end after falling into a vat of acid while attacking his former boss; a bulimic supermodel dies following an uncontrollable binge; and a pornography addict is impaled when an overinflated tire explodes.'),
    'thelightersideofdeath': ('The Lighter Side of Death', "A farmhand lands in trouble with the farmer's daughter; raw snails serve up a nasty surprise; and a magician finally bites the bullet."),
    'thegoodthebadandthedead': ('The Good, The Bad, and the Dead', 'A paranoid survivalist crosses paths with a snake; a shoplifter dives into a dumpster and ends up getting trashed; and a cute girl catches a big one - right down her throat.'),
    'deathbenotstupid': ('Death Be Not Stupid', "A biker downs gasoline; a couple meet their end after making love; a narcoleptic dozes off on the job; a woman's tapeworm diet eats her alive; paintball pranksters meet a fatal blow; and an anxious electrician tries fishing with electricity, and gets the shock of his life."),
    'cureforthecommondeathparti': ('Cure for the Common Death, Part I', 'A redneck meets a fatal end while celebrating the Fourth of July; a man with a taste for metal takes his cravings too far; a pair of heavy metal fans learn the deadly side of headbanging; radium-painted workers glow for fun; two metal fans snort fire ants; and a diver who survives a tank failure is blown apart.'),
    'deathausersmanual': ("Death: A User's Manual", "An overeater goes belly up; a bodybuilder juiced and loses; a young woman texts herself - to death; a golfer has a 'rough' round; a car thief gets left hanging; and a drunk clown pops his own balloon."),
    'iseedeadpeopleandtheyrecrackingmeup': ("I See Dead People (And They're Cracking Me Up)", 'A fatal colonic; a delayed death; and a hot dog thief meets his end.'),
    'deathonarrival': ('Death on Arrival', "A woman's breast implants explode mid-flight; and marijuana and a forklift end a young man's life."),
    'deathbites': ('Death Bites!', 'A chubby chaser lands big; a frat boy suffers frat burn; a fiddler hits a sour note; an ex-con gets exterminated; a French maid dusts her boss; mobsters lose face; and a limp lover goes down hard.'),
    'upwithdeath': ('Up With Death', 'A hot nurse strips down; two trippers get needled; a biker chick goes down; a necrophiliac gets a final nail; a holdup ends in a mix-up; a hockey fight turns bloody; and a raccoon lover gets smitten and bitten.'),
    'puttingahappyfaceondeath': ('Putting a Happy Face on Death', 'A thief hides in a car wash with deadly consequences; and a man cheating at a cockfight is killed by his own rooster.'),
    'bringinginthedead': ('Bringing in the Dead', 'A rapist makes a fatal mistake on a cross-dressing boxer; and hula and belly dancing turn deadly.'),
    'gratefullydead': ('Gratefully Dead', 'An anal compulsive turns repulsive; a purse snatcher takes a tumble; a weightlifter loses his grip; a young goth gets exorcised; a smoker gets smoked; two dopes do themselves (in); and a cow lover gets milked.'),
    'comeongetdeathy': ('Come On, Get Deathy', 'A bliss seeker gets tanked; a little person swallows a harp; a mean hubby goes over the edge; a guitarist gets unplugged; a foolhardy thief breaks his numb-skull; a gold digger digs her own grave; and a spurned lover gets trashed.'),
    'deathwatch': ('Death Watch', 'Hot cheerleaders get buzzed; a B-52 goes down in flames; a speed freak blows his mind; a cat hater gets his head handed to him; a health nut gets ratted out; and a golfing couple suffers some bad fore play.'),
    'wakingupdead': ('Waking Up Dead', 'An acupuncture patient misses the point; a construction worker takes a deadly bathroom break; a stowaway gets his ass-sets frozen; a nagging housewife blows her own fuse; and a cheating gambler gets squeezed.'),
    'youredeadlol': ("You're Dead! LOL!", 'The Samurai Death Squad loses a member; a moron gets smoked by cigarettes; a remote glider backfires; a rejected boyfriend faces rejection; a dog walker gets hounded to death; and a biker sparks a riot.'),
    'deadtorights': ('Dead to Rights', 'A man with anger issues dies three ways at once; and death results when a teen purse snatcher meets an elderly taekwondo master.'),
    'deadondead': ('Dead on Dead', 'Two drug smugglers get in hot water in the South Pacific; and the CIA zaps a terrorist with a gamma ray gun.'),
    'deathonastick': ('Death on a Stick', 'A peeper takes a bath; a pool hopper goes belly-up; three soldiers get blown up; a gigolo gums up; a bachelorette takes a mouthful; a monk tangles with a donkey; and a boy band hits rock bottom.'),
    'puttingasmileyfaceondeath': ('Putting A Smiley Face On Death', 'A liposuction among friends goes wrong; a crude boss takes a leak and bleeds out; a proctologist gets rear-ended; a line-crossing Viking gets split open; a waiter makes a fatal mistake; a woman grabs attention, but bolts too fast; and a hippie gets road killed.'),
    'stupidisasstupiddies': ('Stupid is as Stupid Dies', 'A meth maker loses face; a nudist follows a deadly diet; a sorority girl swallows too much; a survivalist gets the hook; a spider topples a stud; a half-naked football fan gets freeze-framed; and two thrill-seekers lose their heads over piercings.'),
    'deadwrongs': ('Dead Wrongs', 'Two con men get blown away; a sushi chef becomes the butt of the joke; and porn addiction turns deadly.'),
    'fataldistractions': ('Fatal Distractions', 'A drug runner gets a heads up; two stoners get bonged; a glutton goes belly up; a man-baby gets timed out; a nature hater gets turtle waxed; a woman gets down and dirty; and a man-hater gets feminated.'),
    'theendisweird': ('The End is Weird', "A robot maker meets his maker; an exhibitionist goes down in public; Houdini's final escape; a vomit lover gets chunked; a prankster gets pranked; a B-baller finds only death; and a Hollywood star gets drained."),
    'hurryupanddie': ('Hurry Up and Die', 'An organ donor loses a heart; someone gets swept away; trailer trashed; nymphos run wild; a wrestler hits the mat; a mailman goes postal; and a rocker gets high.'),
    'deathputsonaduncecap': ('Death Puts on a Dunce Cap', 'Eating a live octopus; multiple orgasms; a hunter becomes the hunted; a soccer fan gets blown away; a beauty loses her face; and drug addicts get their heads cracked.'),
    'youngdumbandfullofdeath': ('Young, Dumb and Full of Death', 'A salesman sells out; a cokehead gets nosed out; a phony preacher sees the light; a peeper gets hammered; a skateboarder face-plants; a corporate trainer takes a fall; and a dummy gets offed in the woods.'),
    'todaysmenudeepfrieddeath': ("Today's Menu: Deep Fried Death", "Death in the '70s; a thief bites his tongue; a groupie falls for a snake; a juicer gets juiced; Typhoid Mary goes down; a mean girl gets a chubby bunny; and a biker craps out."),
    'cureforthecommondeathpartii': ('Cure for the Common Death, Part II', 'A low rider is crushed; a dummy meets nunchucks; Bigfoot gets the boot; a bikini girl swallows trouble; and a jockey gets tossed.'),
    'suddendeath': ('Sudden Death', 'A Japanese rocker dies onstage; prison escape blows up; a scorned roommate gets revenge; a vain dancer bites the dust; clueless terrorists melt down; a foolish hard hat falls; and a tall man squeezed out in Medieval England.'),
    'dyingtotellthestory': ('Dying to Tell the Story', "A couple gets antsy on safari; a braggart's new truck turns on him; a surfer is board to death; and a chess master meets his match."),
    'ifyouredeadleaveamessageandwellgetbacktoyou': ("If You're Dead - Leave a Message and We'll Get Back to You", "A hat maker doesn't make it; a tech geek gets uninstalled; a wannabe hip-hop queen gets butted out; a carjacker gets jacked off; a pretend gangbanger gets body-slammed; a scam artist's plan gets crushed; and an agro dad gets blanked."),
    'theoneaboutdumbpeopledying': ('The One About Dumb People Dying', 'A crossdresser "wets" the bed; a gymnast makes a killer move; a greedy crematorium worker explodes; a man drinking liquid cocaine gets a deadly kick; a stewardess is in over her head; a taxidermist gets squirrely; and a pumpkin thief takes theft to the heart.'),
    'gettingarisefromthedead': ('Getting a Rise from the Dead', 'A sign spinner spins out; a recipe thief gets her goose cooked; cloud seeding turns rocky; a tobacco chewer gets chewed out; a mob hit goes awry; a corporate spy hits the fan; and a mad scientist gets reanimated.'),
    'readyornotherecomesdeath': ('Ready or Not, Here Comes Death', 'A Japanese game show contestant gets deep-sixed; a free runner runs out of time; a mean caretaker gets pickled; a stripper with big boobies meets her end; a softballer busts a gut; a murderer busts out of the nut house; and two hunters get dogged.'),
    'graveerrors': ('Grave Errors', "A hairdresser swallows too many 'leg spreaders'; Katrina looters get a shock; 1920s pipe-hitting homeboys; a fake doctor meets a leper; a mistress loses face; and a cell phone user gets disconnected."),
    'killingthemsoftly': ('Killing Them Softly', 'An email scammer gets deleted; a hot co-ed flunks out; a grave robber digs his own grave; a warlord snorts crystal death; a couple screws themselves to death mid-air; two losers suck and blow up; and an old Nazi meets an old bullet.'),
    'betterthemthanus': ('Better Them Than Us', 'A millionaire bottoms out; a Russian pimp struggles; gang bangers play doctor; a pyromaniac gets burned; an ice cream man gets iced; a bad actor loses a hand; and a Greek meets his brass.'),
    'deadbeforetheyknowit': ('Dead Before They Know It', 'Death crashes a terrorist wedding; a big box squashes small heads; a self-blood transfusion goes wrong; a gangster spills his guts; a French killer loses his head; and a very bad Santa gets iced.'),
    'stupidisasdeathdoes': ('Stupid Is as Death Does', 'A deadbeat dad goes through the roof; a stump lover gets eyeballed; a drinking game turns deadly; a dummy goes from spying to dying; a gamer gets pwned; a mover stops moving; and a poser artist explodes onto the scene.'),
    'thatsmisterdeath': ('That\'s "Mister Death', 'A jersey chaser gets plugged; OCD stands for "of course (you\'re) dead"; a terrorist eats himself to death; an animal abuser gets dog-boned; a massage parlor patron meets an unhappy end; two inmates lynch themselves; and a bank robber loses his head.'),
    'deaththenewblack': ('Death, the New Black', 'A disco king hits the floor; a sauna contest goes gaseous; an upskirting perv gets busted; a meathead blows himself (up); a pot farmer gets munchied; a football coach splits his uprights; and a drunk heckler gets fleshed out.'),
    'deathbealadytonight': ('Death Be a Lady Tonight', 'An annoying guy gets cut down; a stalker gets smoked out; a football fanatic goes down in a barfight; a drug addict gets crushed; and a tomb raider goes batty.'),
    'todaysspecialdeath': ("Today's Special: Death", "A hot welder goes down on the job; an unfaithful wife can't cheat death; a '20s gangster gets steamed; and a mother-in-law from hell goes back."),
    'eatpraydie': ('Eat, Pray, Die', 'A medieval German gets stoned; a bachelor gets butted out; a con man guru flames out; a dog hater gets boned; and a juvenile delinquent hates Farmville.'),
    'waitdonttellmeyouredead': ("Wait, Don't Tell Me? You're Dead!", "A neo-Nazi opens a can of whoop-ass; a prankster's joke backfires; a voyeur gets fooled; a stalker gets shafted; and an epileptic stripper goes lights out."),
    'deaththegiftthatlastsforever': ('Death - The Gift That Lasts Forever', "A cheatin' hubby gets eaten by a bear; an old pervert sex-plodes; a bride goes down at the altar; a package thief meets an anthrax surprise; an insomniac hits and runs; a bearded hipster drowns; and a drunk worker's pants explode."),
    'deathonesizefitsall': ('Death: One Size Fits All', 'A fake handicapped man gets his comeuppance; a con man is frozen; a female wrestler goes down; a driving teacher loses control; and a mine foreman explodes.'),
    'deathbyrequest': ('Death by Request', '1000 Ways to Die presents a new award show... "The Deathies", featuring selected deaths: Sexiest Death: "Washed and Fried" ( Winner ) "Blood Bath & Beyond" (Runner-Up A) "Gum\'s The Word" (Runner-Up B) Historical Death: "Back Stabbed" ( Winner ) "Vike-O-Done" (Runner-Up A) "My Big Fat Greek Death" (Runner-Up B) Death During Sex: "Ass Phyxiated" ( Winner ) "Gasketballed" (Runner-Up A) "Orspasm" (Runner-Up B) Cosmic Karma: "Steward-death" ( Winner ) "Dead Meat-eorite" (Runner-Up A) "Road Killed" (Runner-Up B) Worst Pervert: "Vom-ate-dead" ( Winner ) "Crib Your Enthusiasm" (Runner-Up A) "Mercury in Uranus" (Runner-Up B) Sports Death: "Dead Eye" ( Winner ) "Samurai Death Squad" (Runner-Up A) "Pam Caked!" (Runner-Up B) Dumbest Druggie: "Em-Bear-Assed" ( Winner ) "Curl Up And Die" (Runner-Up A) "Fecal Attraction" (Runner-Up B) Dumbest Death: "Boys 2 Dead" ( Winner ) "Bitch Zapped" (Runner-Up A) "Midnight Choker" (Runner-Up B) Most Painful Death: "Bad Max" ( Winner ) "Easy Slider" (Runner-Up A) "Bot-ily Harm" (Runner-Up B) Deathiest Death: "Titty Titty Bang Bang" ( Winner ) "Fat-ality" (Runner-Up A) "Chippin\' Dale" (Runner-Up B)'),
    'deadliestkitsch': ('Deadliest Kitsch', 'A dictator gets stuck; a security guard gets hosed; a cyclist runs out of breath; a rock climber falls; and a circus clown meets an insane posse.'),
    'gravedecisions': ('Grave Decisions', 'A politico has a sneezing fit; a gun-toting senior blows up; a road-rage woman takes one in the gut; a convict meets a shocking end; a dirty biker gets their due; and a camper boils over with love.'),
    'dirtnap': ('Dirt Nap', "A bank robber sticks his neck out; a redhead gets taken down; a tough teen meets a mailbox; a shyster shopper takes a dip; a fat man loses face; a crazy ex gets ex'd; and a farting contest turns fatal."),
    'deathtakesavacation': ('Death Takes a Vacation', 'A bouncer gets beamed; a Japanese rockstar sparks suicide; a food vendor gets deep fried; a chemical owner tries to stop a leak; a drug smuggler meets a lethal tie-dye; a mime gets pickled; and a tennis girl hits her target.'),
    'wildwilddeath': ('Wild Wild Death', "A bank robber fails badly; a fake superhero falls; a guy dies chasing views; a supervisor's date goes wrong; an art thief gets glassed; a paramedic gets high - and shocks himself dead; and a sex blogger hickeys herself to a stroke."),
    'deathpenalties': ('Death Penalties', 'A wedding singer gets choked up; a French maid trapped in an iron maiden; a chef loses face; and a muscle woman meets her maker.'),
    'dieabetic': ('Die-abetic', "A lady puckers up one last time; a tow truck driver becomes a head banger; a waitress gets a bad tip; a food critic misses the point; a turkey meets a turkey; a neck massager takes a woman's breath away; and a dancer loses heart."),
    'stardeaththelastgeneration': ('Star Death: The Last Generation', "A cat lady's love goes too fur; a burglar falls for his victim; a mob boss gets the finger; a nasty supermodel meets a dead eye; a customer is left breathless by great savings; a perfectionist overhydrates; and a man rolls over the point."),
    'deathputtingthefun': ('Death: Putting the "Fun', 'Trainer and barbells collide; a polygamist falls into his own trap; a couple wine and die; and a ticket scalper meets a red light.'),
    'sordeadaffair': ('Sor-Dead Affair', 'A man gets frisky with a statue; a rioter gets the wind knocked out; a sleepwalker goes for a swim; and a man dies with a happy ending.'),
    'lockedandlowdead': ('Locked and Low Dead', 'Socialite goes green; a short-fused man finally blows; a woman high-jumps to her death; a crooked cop reeks of decay; a wormy scam artist; a trippy trip to the market; and a bumbling mad scientist gets burned.'),
    'entertheferret': ('Enter the Ferret', 'A ferret goes up the eerie canal; a fat man squeezes into a baby swing; a female boxer goes down; a stoner gets launched; a bad man takes an acid bath; a food fight turns deadly; and a tattoo artist swallows a chain.'),
    'thinkgloballydielocally': ('Think Globally, Die Locally', "A Chinese rapper gets grilled; a mini-golfer maxes out; a super lotto winner goes super nuts; a yoga teacher is a real gas; a hipster goes down in slo-mo; a hacker gets hacked; and a warden can't lock it down."),
    'tweetsfromthedead': ('Tweets From the Dead', 'An exterminator gets exterminated; a stockbroker turns magnetic in the stomach; a wedding crasher crashes through the glass; a thief meets a meathook; a black marketeer gets blown up; a hijacker is exploded by a semi; and a ghost buster gets busted.'),
    'anewappcalleddeath': ('A New App Called Death', 'A sexy copier mishap; a scavenger loses his head; a bicycle hater gets hit; milking a pig; a winded diva; and a motel inspector stirs the dead.'),
    'deathcertificates': ('Death Certificates', 'A fitness instructor gets bounced; a bird smuggler catches the flu; coke mules get branded; a couple takes a hit; a computer thief crashes and burns; a moonshiner gets poked; and a director makes a scene.'),
    'cryingoverspilledblood': ('Crying Over Spilled Blood', 'A tennis brat gets the shaft; a sadistic loan officer; a dead-eye sniper; ghost peppers; a deadly infomercial; a jailbreak gone wrong; and a caveman discovers fire.'),
    'itsadeaddeaddeadworld': ("It's a Dead, Dead, Dead World", 'A lazy husband goes on a roll; terrorists get gassed; a germaphobe takes a deadly bath; and death hits the Jersey Shore.'),
    'deaththefinalfrontier': ('Death, The Final Frontier', 'A tease gets stoned; a drunk wife crashes a sobriety party; a filthy husband falls for a chainsaw; a garage sale turns deadly; and a strongman gets weak in the knees.'),
}

# ── Dragon Ball (1986): TMDB titles, IMDb synopses, Wikipedia saga per episode; one season S01 E1-153 ──
DRAGON_BALL = [  # index = absolute episode - 1 (feed: "Dragon Ball 003"): (saga, name, synopsis)
    ('Emperor Pilaf Saga', 'The Secret of the Dragon Balls', "Isolated martial artist Goku crosses paths with treasure-hunter Bulma, launching an unlikely duo's quest for the mythic Dragon Balls."),
    ('Emperor Pilaf Saga', "The Emperor's Quest", "On the road to the Dragon Balls, Goku and Bulma make camp, brave the wilds, and meet a lost sea turtle -- unaware Pilaf's minions are scouting a mysterious glow nearby."),
    ('Emperor Pilaf Saga', 'The Nimbus Cloud of Roshi', "Goku and Bulma help a lost sea turtle return home. As a reward, its master, the Turtle Hermit, offers Goku a magical flying cloud, but only if he can prove he's pure of heart."),
    ('Emperor Pilaf Saga', 'Oolong the Terrible', 'Goku and Bulma arrive at a village terrorized by the shape-shifting Oolong, who has been kidnapping young women. To stop him and retrieve a Dragon Ball, Goku disguises himself as a girl to confront the mischievous pig.'),
    ('Emperor Pilaf Saga', 'Yamcha the Desert Bandit', "While crossing the Diablo Desert, Goku, Bulma, and Oolong are ambushed by Yamcha, a desert bandit, and his shape-shifting companion, Puar. A fierce battle ensues, but Yamcha's fear of women unexpectedly turns the tide."),
    ('Emperor Pilaf Saga', 'Keep an Eye on the Dragon Balls', "Goku and friends continue across the desert, unaware that Yamcha is secretly trailing them. Meanwhile, Oolong's cowardice and Bulma's capsule mix-up lead to awkward mishaps as the hunt for the Dragon Balls continues."),
    ('Emperor Pilaf Saga', 'The Ox King on Fire Mountain', "Goku, Bulma, and Oolong reach Fire Mountain, where they meet the fearsome Ox-King. When Goku's identity is revealed, the Ox-King asks him to retrieve the Bansho Fan from Master Roshi to put out the flames."),
    ('Emperor Pilaf Saga', 'The Kamehameha Wave', "Goku and Chi-Chi return to Master Roshi's island to obtain the Bansho Fan, only to learn it's been discarded. Determined to help, Roshi accompanies them to Fire Mountain and unveils his powerful Kamehameha wave to extinguish the flames."),
    ('Emperor Pilaf Saga', "Boss Rabbit's Magic Touch", 'Son Goku, Bulma and Oolong arrive at a village in which the villagers seem scared of Bulma. It is soon found out to be due to her outfit having the rabbit ears associated with the Rabbit Gang, lead by Usagi Ninjinka.'),
    ('Emperor Pilaf Saga', 'The Dragon Balls are Stolen!', "Shu runs off with Bulma's suitcase, which contains their Dragon Balls. Luckily, Goku still has the Four-Star Ball."),
    ('Emperor Pilaf Saga', 'The Penalty is Pinball', 'Mai steals the Four-Star Ball from Goku. When they wake up, Pilaf sends giant pinballs rolling after them.'),
    ('Emperor Pilaf Saga', 'A Wish to the Eternal Dragon', 'To stop Emperor Pilaf, Oolong interrupts his wish for world conquest with a wish for underpants. A furious Pilaf orders them burned to death. Then Goku looks up at the full moon and unleashes an ancient evil.'),
    ('Emperor Pilaf Saga', 'The Legend of Goku', "Goku, now the Great Ape, begins destroying Pilaf's castle. Bulma, Yamcha, Oolong, and Puar are able to escape as Pilaf, Mai, and Shu start attacking Goku."),
    ('Tournament Saga', "Goku's Rival", "Goku heads towards Master Roshi's island. Suddenly, another boy named Krillin requests training from Master Roshi."),
    ('Tournament Saga', 'Look Out for Launch', "Goku and Krillin bring Launch back to Master Roshi's island. Unknown to either of them, when she sneezes, she turns into a violent blonde criminal."),
    ('Tournament Saga', 'Find That Stone!', 'Master Roshi gives the boys their final test for the day. He throws a stone into the woods, telling them to find it, and the loser must go without dinner.'),
    ('Tournament Saga', 'Milk Delivery', 'Master Roshi has the boys deliver milk in many exhausting runs.'),
    ('Tournament Saga', 'The Turtle Hermit Way', 'Goku and Krillin continue their intense training.'),
    ('Tournament Saga', 'The Tournament Begins', 'After months of training with heavy turtle shells, the boys are eager to learn fighting techniques in time for the 21st World Martial Arts Tournament.'),
    ('Tournament Saga', 'Elimination Round', 'The preliminaries of the 21st World Martial Arts Tournament begin with Goku, Krillin, and Yamcha eager to advance.'),
    ('Tournament Saga', 'Smells Like Trouble', 'In the quarterfinal matches, Krillin is in the first match against Bacterian, a giant whose stench overwhelms the enemy.'),
    ('Tournament Saga', 'Quarterfinals Begin', 'In the quarterfinals, Yamcha fights the powerful Jackie Chun. Nam fights Ranfan, who relies on seduction to win.'),
    ('Tournament Saga', 'Monster Beast Giran', "Goku's quarterfinal opponent, the monstrous Giran fights him with cheating tactics."),
    ('Tournament Saga', "Krillin's Frantic Attack!", 'The semifinals begin as Krillin and Jackie Chun fight.'),
    ('Tournament Saga', 'Danger From Above', 'Goku starts his semifinal match against Nam, who uses aerial attacks.'),
    ('Tournament Saga', 'The Grand Finals', 'After many impressive battles, the final match of the World Martial Arts Tournament has finally arrived. This ultimate showdown features crafty veteran Jackie Chun taking on the rambunctious youngster Goku.'),
    ('Tournament Saga', 'Number One Under the Moon?', "The final match between Goku and Jackie Chun continues as Jackie's hypnosis and Goku's janken fail to yield results. They are then forced to unleash their deadliest techniques."),
    ('Tournament Saga', 'The Final Blow', 'Jackie Chun reveals that the actual target of his Kamehameha wave was the moon, to de-power Goku. With both of them exhausted, they agree on a straightforward finish to the fight.'),
    ('Red Ribbon Army Saga', 'The Roaming Lake', "The river at Nam's village has run dry, and Goku finds that a dam has been built upstream by Giran and his fellow monsters."),
    ('Red Ribbon Army Saga', 'Pilaf and the Mystery Force', 'When the dragon radar is stolen, Goku follows the thief to to an antique shop with a Dragon Ball.'),
    ('Red Ribbon Army Saga', 'Wedding Plans?', "The much pursued Dragon Ball ends up in the possession of the great and powerful Ox-King – who just happens to be busy planning his daughter's wedding."),
    ('Red Ribbon Army Saga', 'The Flying Fortress - Vanished!', 'Both the Red Ribbon Army and Goku pursue Pilaf for the Dragon Ball.'),
    ('Red Ribbon Army Saga', 'The Legend of a Dragon', "As Goku searches for the Dragon Balls, he aids a group of monkeys threatened by the Red Ribbon Army. Meanwhile, Master Roshi shares an ancient legend about the Dragon Balls' origin."),
    ('Red Ribbon Army Saga', 'Cruel General Red', "As Goku closes in on the Red Ribbon Army's base, General Red's ruthless ambition comes into focus. Meanwhile, Commander Red's true, selfish reason for collecting the Dragon Balls is shockingly revealed."),
    ('Red Ribbon Army Saga', 'Cold Reception', 'The girl called Snow explains to Goku that the Red Ribbon Army is forcing their village to help them look for the Dragon Ball.'),
    ('Red Ribbon Army Saga', 'Major Metallitron', 'Goku reaches the third floor of Muscle Tower and faces Major Metallitron, a massive android who shrugs off even a Kamehameha. With brute force failing, Goku must outthink the mechanical menace to continue his rescue mission.'),
    ('Red Ribbon Army Saga', 'Ninja Murasaki is Coming!', "Goku ascends to the fourth floor of Muscle Tower, entering a forested arena. There, he faces Ninja Murasaki, a cunning adversary who employs deceptive tactics and surprise attacks to thwart Goku's rescue mission."),
    ('Red Ribbon Army Saga', 'Five Murasakis', 'Goku faces off against Ninja Murasaki inside Muscle Tower, but the fight takes a strange turn when four more identical Murasakis appear, forcing Goku into a bizarre five-on-one ninja battle.'),
    ('Red Ribbon Army Saga', 'Mysterious Android No. 8', "Goku confronts the gentle Android 8, who refuses to fight. Together, they navigate Muscle Tower's deadly traps, aiming to rescue the village chief from the Red Ribbon Army's clutches."),
    ('Red Ribbon Army Saga', 'Horrifying Buyon', "Goku and Android 8 fall into a hidden floor of Muscle Tower, where General White unleashes the grotesque monster Buyon. Goku's punches bounce off, forcing him to improvise against the rubbery foe."),
    ('Red Ribbon Army Saga', 'The Fall of Muscle Tower', "Goku confronts General White on Muscle Tower's top floor. When White resorts to underhanded tactics, Android 8 intervenes, leading to a decisive showdown that could bring down the entire tower."),
    ('Red Ribbon Army Saga', 'The Secret of Dr. Flappe', 'Eighter still has the bomb inside him, so they go to Dr. Flappe to sort the problem as Murasaki stalks them.'),
    ('Red Ribbon Army Saga', 'A Trip to the City', 'Goku reaches West City but has no idea where to find Bulma.'),
    ('Red Ribbon Army Saga', 'Master Thief, Hasky', 'General Black hires a master thief, Hasky, to get the balls from Goku.'),
    ('Red Ribbon Army Saga', 'Danger in the Air', 'Goku and friends enjoy an amusement park outing until a cunning thief targets his Dragon Balls with a mid-air trap.'),
    ('General Blue Saga', "Bulma's Bad Day", "Goku dives for an undersea Dragon Ball off a remote island, while Bulma's brush with the Red Ribbon Army draws General Blue's attention."),
    ('General Blue Saga', 'Kame House - Found!', "Seeking help to retrieve a Dragon Ball from the ocean floor, Goku and Bulma head to Master Roshi's island, unaware the Red Ribbon Army is closing in."),
    ('General Blue Saga', 'Deep Blue Sea', 'Goku, Bulma, and Krillin hunt a Dragon Ball beneath the waves, but General Blue and the Red Ribbon Army close in, turning their submarine quest into a perilous cat-and-mouse chase.'),
    ('General Blue Saga', 'Roshi Surprise', 'Goku, Bulma, and Krillin search an underwater pirate cave for a Dragon Ball while the Red Ribbon Army raids Kame House, leaving Master Roshi and Launch to deal with unwelcome visitors.'),
    ('General Blue Saga', 'The Trap is Sprung', 'Chasing a Dragon Ball into an underwater pirate stronghold, Goku, Bulma, and Krillin face a gauntlet of traps -- while General Blue closes in.'),
    ('General Blue Saga', 'Beware of Robot', 'Deep in a submerged pirate cave, Goku, Bulma, and Krillin brave lethal traps and a giant pirate robot as General Blue closes in on a long-lost Dragon Ball.'),
    ('General Blue Saga', 'The Pirate Treasure', 'Exploring a sunken pirate hideout, Goku, Bulma, and Krillin hunt a Dragon Ball through lethal traps as a relentless Red Ribbon officer shadows their every move.'),
    ('General Blue Saga', 'Blue, Black and Blue', 'In a booby-trapped pirate cave, Goku faces General Blue while Bulma and Krillin search for a Dragon Ball and a way out.'),
    ('General Blue Saga', 'Escape From Pirate Cave', 'With traps primed and time running out, Goku, Krillin, and Bulma scramble to escape a collapsing pirate cavern -- all while a relentless adversary dogs their every step.'),
    ('General Blue Saga', 'Penguin Village', "Goku's pursuit of General Blue steers Nimbus into the off-beat Penguin Village, where bizarre locals and slapstick surprises complicate his hunt for the Dragon Balls."),
    ('General Blue Saga', 'Strange Visitor', "Lost in Penguin Village, Goku teams with Arale and the Gatchans to chase General Blue; Arale's antics blow his cover, and Senbei Norimaki races to mend Goku's smashed Dragon Radar."),
    ('General Blue Saga', 'Arale vs. Blue', "General Blue infiltrates Penguin Village to swipe Goku's newly fixed Dragon Radar, but bumbling inventor Senbei and unstoppable Arale turn the theft into a madcap chase that leaves the Red Ribbon elite begging for mercy."),
    ('Commander Red Saga', 'The Land of Korin', "In the Sacred Land of Korin, the Red Ribbon Army sends Captain Yellow to seize a Dragon Ball, but guardian Bora and his son stand firm; Goku's sudden arrival on Nimbus ignites a clash that could upend the Army's plans."),
    ('Commander Red Saga', 'The Notorious Mercenary', "To silence Goku and reclaim the Dragon Balls, the Red Ribbon Army hires legendary assassin Tao Pai Pai, whose ruthless arrival at Korin's sacred land pits him against protector Bora -- and sets Goku on a deadly collision course."),
    ('Commander Red Saga', 'Tao Attacks!', 'With the Dragon Balls in his sights, ruthless assassin Mercenary Tao confronts Goku, sparking a clash of signature techniques and propelling the young warrior toward a perilous ascent of the legendary Korin Tower.'),
    ('Commander Red Saga', 'Korin Tower', 'In pursuit of the legendary Sacred Water, Goku undertakes the perilous climb of Korin Tower, pushing body and spirit toward new heights.'),
    ('Commander Red Saga', 'Sacred Water', 'Scaling Korin Tower, Goku battles fatigue and a mischievous master in pursuit of a power that could change everything.'),
    ('Commander Red Saga', 'The Return of Goku', 'After intense training atop Korin Tower, Goku rushes back to the Sacred Land to protect Upa and reclaim the four-star Dragon Ball, sparking a high-stakes rematch with the ruthless Mercenary Tao.'),
    ('Commander Red Saga', 'The Last of Mercenary Tao', "Unable to beat Goku, Mercenary Tao scales Korin Tower seeking the Sacred Water's power, but the wily guardian cat has other plans -- while Goku and Upa await the next round."),
    ('Commander Red Saga', 'Confront the Red Ribbon Army', "Goku races toward the Red Ribbon Army's headquarters as Colonel Violet hunts a Dragon Ball, setting the stage for a looming clash."),
    ('Commander Red Saga', 'A Real Bind', "Goku heads to Red Ribbon Army HQ to reclaim the Dragon Balls as Commander Red scrambles his forces and Goku's friends race to back him up, setting the stage for a high-stakes showdown."),
    ('Commander Red Saga', 'The End of Commander Red', "Goku storms the Red Ribbon Army's headquarters, plunging the fortress into chaos as panicked troops scatter and a power struggle brews, setting the stage for a decisive clash."),
    ('Commander Red Saga', 'The Last Dragon Ball', "With the final Dragon Ball in sight, Goku storms the Red Ribbon Army HQ and faces Staff Officer Black's colossal battle suit, turning the hunt into a perilous showdown."),
    ('Fortuneteller Baba Saga', 'Who is Fortuneteller Baba?', "With the final Dragon Ball missing from Bulma's radar, Goku and friends seek the elusive Fortuneteller Baba -- only to learn her help comes at a price."),
    ('Fortuneteller Baba Saga', 'We are the Five Warriors', "At Fortuneteller Baba's palace, Goku's team must face her spooky fighters one by one; winning could reveal the last Dragon Ball's location."),
    ('Fortuneteller Baba Saga', 'Deadly Battle', "In Fortuneteller Baba's arena, Yamcha duels an invisible foe as Goku rushes to rally help; the team pushes through the gauntlet for the final Dragon Ball's clue."),
    ('Fortuneteller Baba Saga', "Goku's Turn", "Fortuneteller Baba's next challenge pits Yamcha against a swift, relentless mummy atop the Devil's Toilet; with the final Dragon Ball at stake, Goku readies himself to enter the fray."),
    ('Fortuneteller Baba Saga', 'The Devilmite Beam', "At Fortuneteller Baba's arena, Goku faces a devilish challenger whose deadly technique targets the darkness in one's heart -- with the final Dragon Ball's location on the line."),
    ('Fortuneteller Baba Saga', 'The Mysterious Fifth Man', "Goku goes head-to-head with Spike the Devilman, a winged freak known for feeding off negative vibes. If the little man survives, there's a fifth fighter waiting in the wings, and he smells strangely familiar."),
    ('Fortuneteller Baba Saga', 'The Strong Ones', "At Fortuneteller Baba's tournament, the final match pits Goku against a mysterious masked fighter -- whose uncannily familiar style leaves Master Roshi uneasy."),
    ('Fortuneteller Baba Saga', 'True Colors of the Masked Man', "At Fortuneteller Baba's arena, Goku duels a mysterious masked warrior while Pilaf, Shu, and Mai set a new scheme in motion for the Dragon Balls."),
    ('Fortuneteller Baba Saga', "Pilaf's Tactics", 'Pilaf, Shu, and Mai challenge Goku to a winner-take-all bet, deploying robot suits to exploit his supposed weakness and snatch the Dragon Balls.'),
    ('Fortuneteller Baba Saga', 'The Eternal Dragon Rises', 'With all seven Dragon Balls collected, Goku and Upa head to the Land of Korin to summon the Eternal Dragon, while Yamcha seeks fresh training under Master Roshi.'),
    ('Fortuneteller Baba Saga', 'Terror and Plague', "Goku answers a little girl's plea and heads to a village terrorized by two bandits and their mysterious gourd -- where outsmarting their tricks matters as much as raw power."),
    ('Fortuneteller Baba Saga', 'Goku vs. Sky Dragon', 'On the road, Goku is drawn into a rivalry between martial arts schools and volunteers to represent a struggling master, squaring off against Sky Dragon before the king.'),
    ('Fortuneteller Baba Saga', 'Goku Goes to Demon Land', "Goku arrives in a village plagued by demons. After its princess is dragged into Demon Land, he ventures through the portal to challenge the realm's ruler and attempt a rescue."),
    ('Fortuneteller Baba Saga', 'The Rampage of InoShikaCho', 'Goku meets a family fleeing a village terrorized by InoShikaCho and rushes to stop the beast -- only to find two mysterious fighters already on the scene.'),
    ('Fortuneteller Baba Saga', 'Which Way to Papaya Island?', 'On the eve of the World Martial Arts Tournament, Goku races to Papaya Island, but a run-in with street hustlers -- and a new friend -- turns the trip into a test of his wits as much as his fists.'),
    ('Tien Shinhan Saga', 'Rivals and Arrivals', 'On Papaya Island for the World Martial Arts Tournament, the gang checks in as Goku races the registration deadline, and familiar rivals arrive to set the stage for the preliminaries.'),
    ('Tien Shinhan Saga', 'Preliminary Peril', "The preliminaries kick off at the World Martial Arts Tournament; Goku, Krillin, Yamcha, and Jackie Chun face early tests as the Crane School's Tien Shinhan and Chiaotzu arrive, igniting tensions and hinting at rivalries to come."),
    ('Tien Shinhan Saga', 'Then There Were Eight', 'As the World Martial Arts Tournament preliminaries wrap up, Goku faces King Chappa while Krillin and Yamcha fight for places among the final eight.'),
    ('Tien Shinhan Saga', 'Yamcha vs. Tien', 'At the 22nd World Martial Arts Tournament, the finalists draw lots and tensions between rival schools erupt as Yamcha and Tien square off in the opening bout.'),
    ('Tien Shinhan Saga', "Yamcha's Big Break", 'The Quarterfinals kick off as Yamcha takes on the formidable Tien Shinhan at the 22nd World Martial Arts Tournament -- a clash of styles and pride that hints at unseen techniques and higher stakes ahead.'),
    ('Tien Shinhan Saga', 'Full-Moon Vengeance', 'At the World Martial Arts Tournament, Jackie Chun faces Man-Wolf, a vengeful challenger driven by a full-moon grudge, in an offbeat bout where clever tactics matter as much as raw power.'),
    ('Tien Shinhan Saga', 'The Dodon Wave', 'At the 22nd World Martial Arts Tournament, Krillin faces the enigmatic Chiaotzu, whose psychic powers and the Dodon Ray put Crane School techniques on display as rival students and masters look on.'),
    ('Tien Shinhan Saga', 'Counting Controversy!!', "At the 22nd World Martial Arts Tournament, Krillin faces Chiaotzu's unnerving psychic techniques, turning the match into a battle of wits, while trouble for Goku brews outside the ring."),
    ('Tien Shinhan Saga', 'Goku Enters the Ring', "At the 22nd World Martial Arts Tournament, Goku's quarterfinal against movie star Pomput is threatened when a shady manager schemes to keep him from the ring."),
    ('Tien Shinhan Saga', 'Tien Shinhan vs. Jackie Chun', 'The first semifinal begins at the World Martial Arts Tournament, pitting Tien Shinhan against the enigmatic Jackie Chun in a showcase of high-level techniques and mind games.'),
    ('Tien Shinhan Saga', 'Stepping Down', "At the 22nd World Martial Arts Tournament, Jackie Chun and Tien Shinhan's semifinal intensifies -- blinding techniques, clever counters, and a clash of ideals keep the arena on edge."),
    ('Tien Shinhan Saga', 'Goku vs. Krillin', 'At the World Martial Arts Tournament, Goku and Krillin face each other in a spirited semifinal match that balances rivalry and respect, showcasing how far both have come.'),
    ('Tien Shinhan Saga', "Tail's Tale", 'At the 22nd World Martial Arts Tournament, friends-turned-rivals Goku and Krillin face off in a fast semifinal where speed and strategy test their bond and push both fighters to new limits.'),
    ('Tien Shinhan Saga', 'Final Match: Goku vs. Tien', 'At the 22nd World Martial Arts Tournament, the final begins: Goku vs. Tien. Friends scramble for seats as the rivals mix speed, skill, and strategy, setting the stage for a fierce, high-stakes duel.'),
    ('Tien Shinhan Saga', "Victory's Edge", 'World Martial Arts Tournament final: Tien Shinhan unveils his "Volleyball Fist" against Goku, who answers with newfound intensity, pushing both fighters toward their limits.'),
    ('Tien Shinhan Saga', "Tien's Insurrection", 'Goku duels Tien at the 22nd World Martial Arts Tournament, a high-stakes clash that tests skill, pride, and the meaning of a fair fight.'),
    ('Tien Shinhan Saga', 'The Spirit Cannon', 'At the 22nd World Martial Arts Tournament, Goku and Tien push their match to new heights, unveiling surprising techniques as pride, endurance, and strategy clash.'),
    ('Tien Shinhan Saga', 'The Fallen', "With the arena obliterated, Goku and Tien's World Martial Arts Tournament final becomes a gravity-defying test of endurance and ingenuity as both push beyond the ring to see who truly stands above."),
    ('King Piccolo Saga', 'Enter King Piccolo', 'After the tournament, a shocking attack sends Goku after a shadowy assailant, while Master Roshi recognizes signs of an ancient evil tied to his past.'),
    ('King Piccolo Saga', 'Tambourine Attacks!', 'King Piccolo sets his plan in motion as his assassin Tambourine hunts tournament fighters; Goku, weakened by hunger, gives chase -- pushing both toward a dangerous encounter.'),
    ('King Piccolo Saga', 'Mark of the Demon', "While Tambourine targets Earth's fighters, King Piccolo sets a new plan in motion for the Dragon Balls. Stranded and starving, Goku encounters a mysterious mountain man who may change his path."),
    ('King Piccolo Saga', 'Here Comes Yajirobe', "Goku's search leads him to the blunt swordsman Yajirobe; when a sinister creature arrives for the Dragon Ball, the two must quickly decide who will face it."),
    ('King Piccolo Saga', 'Terrible Tambourine', "Tambourine's rampage continues with Yamcha in his sights. Master Roshi leads Tien and Chiaotzu to gather the Dragon Balls, while Goku seeks Yajirobe's Dragon Ball."),
    ('King Piccolo Saga', "Tien's Atonement", "Roshi's Dragon Ball hunt leads to a risky deal; Tien crosses paths with an old rival, while Goku's chase after Yajirobe draws a ruthless assassin."),
    ('King Piccolo Saga', "Goku's Revenge", 'At last, Goku confronts Tambourine for a long-awaited rematch, while Roshi and Tien pursue the Dragon Balls as an ominous force closes in.'),
    ('King Piccolo Saga', 'Goku vs. King Piccolo', 'Goku confronts King Piccolo for the first time -- alone and with the Dragon Balls at stake -- as their showdown begins.'),
    ('King Piccolo Saga', 'Piccolo Closes In', "Reeling from his clash with King Piccolo, Goku races for Korin Tower while Master Roshi and Tien set a risky trap to seize the remaining Dragon Balls and halt King Piccolo's reign."),
    ('King Piccolo Saga', "Roshi's Gambit", 'Roshi confronts King Piccolo, betting everything on an ancient sealing technique as the tyrant closes in on the Dragon Balls.'),
    ('King Piccolo Saga', "King Piccolo's Wish", 'With the Eternal Dragon within reach, King Piccolo seeks to make his wish. Tien and Chiaotzu attempt to intervene, while Goku and Yajirobe head for Korin Tower.'),
    ('King Piccolo Saga', 'Siege on Chow Castle', "With King Piccolo bearing down on Chow Castle, Goku and Yajirobe head for Korin's Tower seeking aid, while Tien and friends regroup for the fight ahead."),
    ('King Piccolo Saga', 'Conquest and Power', 'King Piccolo tightens his grip on Earth as Goku and Yajirobe reach Korin Tower for guidance, while Tien rushes to master a risky sealing technique -- and a shaken kingdom faces a grim ultimatum.'),
    ('King Piccolo Saga', 'Awaken Darkness', 'Goku braves an icy labyrinth to find the Ultra Divine Water while a mysterious darkness awakens below.'),
    ('King Piccolo Saga', 'A Taste of Destiny', 'Goku navigates a frozen maze in pursuit of the Ultra Divine Water, confronting deceptive reunions and perilous tests that blur reality from illusion.'),
    ('King Piccolo Saga', 'The Ultimate Sacrifice', "Under King Piccolo's reign, Tien prepares a forbidden technique and sets out to confront him, while Goku, renewed by a perilous trial, launches toward the battle that could decide Earth's fate."),
    ('King Piccolo Saga', 'Prelude to Vengeance', "King Piccolo targets West City as Tien reaches King's Castle -- only to confront a formidable new creation."),
    ('King Piccolo Saga', 'Battle Cry', "As King Piccolo tightens his grip, Tien confronts a brutal new creation at the King's Castle, while Goku races to the battlefield -- stopping to protect loved ones along the way."),
    ('King Piccolo Saga', 'Goku Strikes Back', 'Goku confronts King Piccolo in the capital, igniting a high-stakes showdown as allies race to the scene and the kingdom holds its breath.'),
    ('King Piccolo Saga', 'The Biggest Crisis', "At Central City's King Castle, Goku squares off with King Piccolo in a high-stakes battle as news spreads and his friends race to help."),
    ('King Piccolo Saga', 'Final Showdown', 'Goku stakes everything against King Piccolo in an all-or-nothing showdown, as a ruthless hostage ploy turns the battle into a dangerous gamble.'),
    ('Piccolo Jr. Saga', 'Lost and Found', 'After the King Piccolo crisis, Goku searches for his Power Pole -- the key to reaching a hidden sanctuary above the clouds -- while his friends regroup and the world begins to heal.'),
    ('Piccolo Jr. Saga', 'Temple Above the Clouds', 'Goku ascends the Power Pole to a temple above the clouds, where a serene attendant tests his worth before he can request an audience; meanwhile, reporters descend on Kame House.'),
    ('Piccolo Jr. Saga', "Earth's Guardian Emerges", "Atop the Lookout, Goku's training with Mr. Popo becomes a test of resolve as a mysterious figure challenges his path -- bringing him closer to a way to restore what was lost."),
    ('Piccolo Jr. Saga', 'Eternal Dragon Resurrected', 'As Goku begins training with Kami, the Eternal Dragon is restored and his friends gather to make a pivotal wish -- setting the stage for the next World Martial Arts Tournament.'),
    ('Piccolo Jr. Saga', 'Quicker than Lightning', "Under Kami and Mr. Popo's watch, Goku braves Mount Rumble to claim the Sacred Crown, sharpening a sixth sense to outrun lightning while his friends continue their own training."),
    ('Piccolo Jr. Saga', 'Secret of the Woods', 'Mr. Popo sends Goku into a quiet forest to find a teacher who can train his mind -- not his fists.'),
    ('Piccolo Jr. Saga', 'The Time Room', 'Sent by Mr. Popo into the Time Room, Goku trains in the past and crosses paths with a young Master Roshi and the Crane Hermit.'),
    ('Piccolo Jr. Saga', "Goku's Doll", "Mr. Popo grants Goku's wish for the ultimate sparring partner, forcing him to battle a powerful double while Tien, Krillin, Yamcha and Chiaotzu journey toward Korin Tower to begin their own intense training."),
    ('Piccolo Jr. Saga', 'Walking Their Own Ways', "As Goku trains with Mr. Popo to sharpen his ki sense, Tien, Krillin, Yamcha and Chiaotzu's search for Korin's Tower leads them to a remote village in danger when its sacred mountain suddenly erupts."),
    ('Piccolo Jr. Saga', 'Hotter than Lava', 'As Goku struggles to master his ki under Mr. Popo, Tien, Yamcha, Krillin and Chiaotzu battle an erupting volcano, racing to divert its lava before it engulfs a remote mountain village.'),
    ('Piccolo Jr. Saga', 'Changes', 'After three years of training, Goku, Tien, Krillin, Yamcha and Chiaotzu reunite at the 23rd World Martial Arts Tournament, but a sinister new contestant suggests the real battle is only beginning.'),
    ('Piccolo Jr. Saga', 'Preliminary Peril', 'At the 23rd World Martial Arts Tournament, Goku and his friends enter the brutal preliminaries, where a mysterious young fighter and a long-forgotten enemy raise the stakes for everyone.'),
    ('Piccolo Jr. Saga', 'Battle of the Eight', 'The brutal preliminaries of the 23rd World Martial Arts Tournament reach their climax as returning heroes, vengeful foes and a mysterious girl battle for a coveted place among the final eight fighters.'),
    ('Piccolo Jr. Saga', 'Tien Shinhan vs. Mercenary Tao', 'At the 23rd World Martial Arts Tournament, Tien squares off against his vengeful former master Mercenary Tao, while Goku is matched with a mysterious woman who seems furious with him.'),
    ('Piccolo Jr. Saga', 'Anonymous Proposal', 'At the World Martial Arts Tournament, Goku battles a fierce female fighter entered as "Anonymous." Her anger hints at unfinished business, and she vows to reveal her identity only if Goku can defeat her.'),
    ('Piccolo Jr. Saga', 'The Mysterious Hero', 'At the 23rd World Martial Arts Tournament, Krillin battles the fearsome Piccolo Jr., while Yamcha squares off with a clumsy contender called Hero -- whose odd luck and stumbles may be an act.'),
    ('Piccolo Jr. Saga', 'Rematch', 'At the World Martial Arts Tournament, Yamcha faces the enigmatic Hero, then Goku and Tien kick off their long-awaited rematch.'),
    ('Piccolo Jr. Saga', 'Goku Gains Speed', "At the World Martial Arts Tournament, Goku and Tien's rematch intensifies when Tien's incredible speed corners Goku, prompting an unexpected adjustment and forcing Tien to debut a new technique."),
    ('Piccolo Jr. Saga', 'The Four Faces of Tien', 'Tien uses a new technique to create multiple copies of himself, forcing Goku to fight four opponents at once during their World Martial Arts Tournament rematch.'),
    ('Piccolo Jr. Saga', 'Kami vs. Piccolo', "Goku wants to fight Piccolo Jr., but the tournament's mysterious Hero faces him in the semifinals, setting a dangerous plan in motion that could decide the championship and Earth's fate."),
    ('Piccolo Jr. Saga', 'Battle for the Future', "With the world at stake and Kami's fate uncertain, Goku enters the World Martial Arts Tournament final to battle Piccolo Jr., a ruthless challenger bent on domination."),
    ('Piccolo Jr. Saga', 'Super Kamehameha', 'In the 23rd World Martial Arts Tournament final, Piccolo Jr. threatens the arena with a devastating blast. With the crowd in peril, Goku gathers his strength for an ultimate Super Kamehameha.'),
    ('Piccolo Jr. Saga', 'Junior No More', 'Piccolo reveals his true nature in the World Martial Arts Tournament final, sparking panic. As he transforms and the stadium clears, Goku faces a larger-than-life challenge.'),
    ('Piccolo Jr. Saga', "Goku's Trap", 'As the tournament final intensifies, Goku gambles on a daring strategy against Piccolo, whose mounting fury pushes their battle toward a devastating new level.'),
    ('Piccolo Jr. Saga', 'Goku Hangs On', 'Piccolo resorts to his ultimate attack, destroying the entire island and seemingly Goku.'),
    ('Piccolo Jr. Saga', 'The Victor', 'Piccolo flies to the sky to finish off his nemesis. However, Goku has a surprise in store for him.'),
    ('Piccolo Jr. Saga', 'Dress in Flames', 'Goku and Chichi prepare for their wedding.'),
    ('Piccolo Jr. Saga', 'The Fire-Eater', 'The people are unable to extinguish the fire consuming the castle, so Goku and Chi Chi seek another Bansho fan.'),
    ('Piccolo Jr. Saga', 'Outrageous Octagon', 'Goku and Chi Chi search for the Bansho fan in a snowy mountain.'),
    ('Piccolo Jr. Saga', 'Mystery of the Dark World', "Goku realizes that the fan won't work and he must go to the Dark World."),
    ('Piccolo Jr. Saga', 'The End, the Beginning', 'In the series finale, Goku and Chi Chi fight to make their wedding go as planned.'),
]

# ── Dragon Ball Z: Wikipedia original NA dub titles (uncut re-dub title where the old dub merged
#    episodes, and for 68-74), TMDB sagas / season numbering / synopses (dashes -> en dash) ──
DRAGON_BALL_Z = [  # index = absolute episode - 1 (feed: "Dragon Ball Z 140" = S05 E01): (season, ep, saga, name, synopsis)
    (1, 1, 'Saiyan Saga', 'The New Threat', 'Goku’s quiet life with his family and friends is about to be interrupted. A new threat – a powerful and sinister alien – is on its way to Earth.'),
    (1, 2, 'Saiyan Saga', 'Reunions', 'Goku and Gohan attend a reunion on Roshi’s island, where Goku introduces his son to all of his old friends. The smiles quickly fade, however, as an unexpected visitor – Raditz – lands on the island.'),
    (1, 3, 'Saiyan Saga', "The World's Strongest Team", 'Raditz has kidnapped Gohan, and unless Goku agrees to join the sinister Saiyan, he may never see his son again! All hope is not lost, however, as a second visitor arrives, and Goku forges an unlikely alliance!'),
    (1, 4, 'Saiyan Saga', "Gohan's Hidden Powers", 'Piccolo may have a way to stop Raditz – the Makankosappo! There’s only one problem. He needs time to gather energy for the blast, which means Goku must fight Raditz alone!'),
    (1, 5, 'Saiyan Saga', "Gohan's Rage", 'Gohan unleashes a mighty attack that not even Radtiz can resist! But as quickly as his power appears, it vanishes. When Raditz prepares to strike back, Goku must make the ultimate sacrifice to save his son!'),
    (1, 6, 'Saiyan Saga', 'No Time Like the Present', 'Piccolo takes Gohan into the wild for a harsh training program. Meanwhile, Goku embarks on a new adventure in the next world, as he travels the endless Snake Way to reach the legendary King Kai!'),
    (1, 7, 'Saiyan Saga', 'Day 1', 'Gohan begins his first day of Piccolo’s training. Alone in the wilderness, he must quickly learn to take care of himself. But that isn’t easy when he’s tired, hungry – and being chased by bloodthirsty dinosaurs!'),
    (1, 8, 'Saiyan Saga', 'Gohan Goes Bananas!', 'Korin wants Krillin, Yamcha, Tien, and Chiaotzu to report for special training! Meanwhile, Gohan’s grueling training causes him to undergo a shocking transformation!'),
    (1, 9, 'Saiyan Saga', 'The Strangest Robot', 'To escape a pack of wild animals, Gohan ventures into an ancient cave, where he meets an old Capsule Corp robot. The robot has lived alone in the cave for over 30 years, and he’s not happy to have visitors!'),
    (1, 10, 'Saiyan Saga', 'A New Friend', 'Gohan’s wilderness adventure continues, as he makes a new dinosaur friend! He’s happy to finally have some company until he’s harshly reminded that not all dinosaurs are friendly!'),
    (1, 11, 'Saiyan Saga', 'Trouble on Arlia', 'On planet Arlia, Vegeta and Nappa become prisoners of the tyrant king who rules the planet. After a brief scuffle with the monster Yeddy, the Arlians realize that the two Saiyans are more than they can handle.'),
    (1, 12, 'Saiyan Saga', 'Global Training', 'Gohan spends his day tormenting a T-Rex. Across the planet, Tien and Chiaotzu find their training interrupted by Launch. Meanwhile, Goku tries to find King Kai on Snake Way.'),
    (1, 13, 'Saiyan Saga', 'Goz and Mez', 'Goku encounters two giant ogres who want nothing more than to use the hero as a play toy! If he can defeat their challenges, the ogres vow to show him the way back to Snake Way.'),
    (1, 14, 'Saiyan Saga', "Princess Snake's Hospitality", 'Back on Snake Way, Goku comes across a house he believes might belong to King Kai! Unfortunately, the dwelling is inhabited by Princess Snake, and she’ll do anything to keep Goku as her prisoner forever!'),
    (1, 15, 'Saiyan Saga', 'Dueling Piccolos', 'Piccolo flies off the handle during his fight with Raditz and splits in two! Meanwhile, Gohan decides to take a raft across the sea to visit his mother, gets caught in a storm, and suddenly remembers that he can’t swim!'),
    (1, 16, 'Saiyan Saga', 'Plight of the Children', 'Gohan finds shelter with a gang of orphans living on the run from meddling adults. The group’s leader hatches a plan to take the kids to a safer hiding place, but when the police show up everything goes wrong!'),
    (1, 17, 'Saiyan Saga', 'Showdown in the Past', 'Earth’s top warriors visit Kami’s Pendulum Room where the past, present, and future co-exist. After a trip back in time, they realize they’ll need to train harder to stand a chance against the approaching Saiyans.'),
    (1, 18, 'Saiyan Saga', 'The End of Snake Way', 'Gohan continues training, but a full moon causes the young Saiyan to rampage out of control! Meanwhile, Goku makes it to the end of Snake Way only to mistake a friendly ape named Bubbles for King Kai!'),
    (1, 19, 'Saiyan Saga', 'A Fight Against Gravity... Catch Bubbles!', 'The intense gravity of King Kai’s planet makes Goku’s training difficult, but when he learns that the Saiyans are used to extreme fighting conditions, Goku is inspired to give it his all. Will it be enough?'),
    (1, 20, 'Saiyan Saga', 'The Legend of the Saiyans', 'After Goku struggles to bash Gregory with a hammer, King Kai inspires him with the story of the Saiyan race – and offers to train him personally! Will it be enough to stop the looming Saiyan invasion?'),
    (1, 21, 'Saiyan Saga', 'A Black Day for Planet Earth', 'Goku’s training is complete, so the gang summons the Eternal Dragon to wish him back to life. There’s only one day left before the Saiyans arrive. Unfortunately, it will take Goku two days to return!'),
    (1, 22, 'Saiyan Saga', 'The Battle Begins... Goku Where Are You?', 'Vegeta and Nappa mark their arrival with the destruction of an entire city! When the Z-Fighters confront them, the heroes must face an onslaught of Saibamen under the command of the Saiyans.'),
    (1, 23, 'Saiyan Saga', 'The Saibamen Strike', 'Krillin, Piccolo, and Gohan stand face to face with the sinister Saiyans and their diabolical henchmen. The villains have already proven terrifyingly powerful. Can Earth’s heroes hold out until Goku arrives?'),
    (1, 24, 'Saiyan Saga', 'Nappa... The Invincible?', 'Enraged over the loss of Yamcha, Krillin unleashes a powerful attack that destroys the maniacal Saibamen once and for all. Now Earth’s defenders must battle the Saiyans themselves – starting with Nappa.'),
    (1, 25, 'Saiyan Saga', 'Sacrifice', 'Chiaotzu sacrifices himself to save his friends from Nappa, but when the smoke clears, the villain still stands! Luckily, Tien has one trick left that could forever silence the Saiyan warrior!'),
    (1, 26, 'Saiyan Saga', "Nappa's Rampage", 'Vegeta has called a halt to the fighting, and Nappa uses the time to go on a rampage! Meanwhile, Goku reaches the end of Snake Way and races to rejoin his friends – but is he already too late?'),
    (1, 27, 'Saiyan Saga', "Time's Up!", 'Piccolo, Gohan, and Krillin do their best to stop the Saiyans from finding the Dragon Balls. Meanwhile, Goku rushes back to Earth on the Flying Nimbus, armed with more power than ever before!'),
    (1, 28, 'Saiyan Saga', 'The Return of Goku', 'Piccolo makes the ultimate sacrifice to save Gohan from the rampaging Saiyans. Just when all seems lost, Goku returns to Earth with an incredible new level of power and confronts the invaders.'),
    (1, 29, 'Saiyan Saga', 'Goku Strikes Back', 'Locked in battle with the Saiyans, Goku gives Nappa a brutal demonstration of the training he received from King Kai. Broken and defeated, Nappa must now face the ferocious wrath of Vegeta!'),
    (1, 30, 'Saiyan Saga', 'Goku vs. Vegeta', 'Goku decides to take on mighty Vegeta all by himself! The two appear evenly matched, but both are hiding their true strength. The epic battle is underway – which mighty warrior will claim victory?'),
    (1, 31, 'Saiyan Saga', 'Saiyan Sized Secret', 'Vegeta and Goku continue trading brutal blows, but the action intensifies when Vegeta reveals the secret power of the Saiyans: the ability to transform into a giant, planet-destroying ape!'),
    (1, 32, 'Saiyan Saga', 'Vegeta... Saiyan Style!', 'Goku feels the brunt of Vegeta’s fully-realized Saiyan power! Earth’s greatest hero is left with no choice except to use the Spirit Bomb. If his attack fails, he may find himself completely doomed!'),
    (1, 33, 'Saiyan Saga', 'Hero in the Shadows', 'With Goku caught in the clutches of the giant ape Vegeta, Krillin attacks with his Destructo Disk! When his effort falls short, an unlikely hero steps out of the shadows!'),
    (1, 34, 'Saiyan Saga', "Krillin's Offensive", 'Goku passes the power of the Spirit Bomb to Krillin, who – with King Kai’s guidance – launches the bomb at Vegeta. The Saiyan is sent flying into the sky, but is the evil warrior really gone for good?'),
    (1, 35, 'Saiyan Saga', 'The Battle Ends', 'Vegeta is crushed beneath the full weight of Gohan’s giant ape form! With the Saiyan battered and defeated, Krillin moves to finish the Saiyan with a final blow – but Goku has other plans.'),
    (1, 36, 'Saiyan Saga', 'Picking Up the Pieces', 'The gang mourns the loss of Yamcha, Tien, Chiaotzu, and Piccolo. With Kami gone, Earth’s Dragon Balls have disappeared. Will the surviving heroes find a way to wish their fallen friends back to life?'),
    (1, 37, 'Saiyan Saga', 'Plans for Departure', 'Bulma accidentally destroys the Saiyan spaceship! Luckily, Mr. Popo reveals the existence of another ship that may be able to reach Namek. Can they find it in time, and will the old ship still work if they do?'),
    (1, 38, 'Saiyan Saga', 'Nursing Wounds', 'Goku, Krillin, and Gohan prepare for the return of the Saiyans. Meanwhile, Bulma and Mr. Popo search for a second spaceship capable of transporting her to Planet Namek.'),
    (1, 39, 'Saiyan Saga', 'Friends or Foes?', 'Gohan, Bulma, and Krillin blast off for Planet Namek in search of the magic Dragon Balls, but their journey quickly turns chaotic when they encounter a bizarre situation in the vacuum of space!'),
    (2, 1, 'Namek Saga', 'Held Captive', 'Bulma, Gohan, and Krillin are mistaken for friends of Frieza and taken prisoner by an angry army of children! To regain their freedom and continue on their mission, the gang must convince the kids of their innocence.'),
    (2, 2, 'Namek Saga', 'Look Out Below', 'A near-fatal crash landing turns out to have a silver lining when Bulma, Gohan, and Krillin are rescued by two friendly Namekians who agree to help them locate the seven Dragon Balls.'),
    (2, 3, 'Namek Saga', 'Hunt for a Dragon Ball', 'Gohan, Krillin, and Bulma continue their search for the Dragon Balls with the help of their new friend Zaacro. Back on Earth, Goku has escaped from the hospital to begin training for his upcoming re-match with Vegeta.'),
    (2, 4, 'Namek Saga', "Who's Who?!", 'As Bulma, Krillin, and Gohan close in on the last of the Dragon Balls, they uncover a shocking secret about their Namekian friends. Meanwhile, Goku works to build up his strength, and Vegeta sets his sights on revenge!'),
    (2, 5, 'Namek Saga', 'Touchdown on Namek', 'Bulma, Krillin, and Gohan finally continue their quest to locate all seven Dragon balls. Unfortunately, the gang soon discovers that they aren’t the only ones seeking the magical orbs!'),
    (2, 6, 'Namek Saga', 'Face-off on Namek', 'Krillin, Gohan, and Bulma are horrified to see Vegeta’s space pod land on Planet Namek, but the Saiyan Prince is the least of their problems. Yet another epically evil villain has come to Namek in search of the Dragon Balls!'),
    (2, 7, 'Namek Saga', 'The Ruthless Frieza', 'With the odds are rapidly mounting against them, Krillin and Gohan will need some serious help if they hope to recover the Dragon Balls from Frieza and his henchmen.'),
    (2, 8, 'Namek Saga', 'The Nameks versus Frieza', 'Krillin and Gohan get their first glimpse of Frieza’s cruelty as the villain unleashes his henchmen upon an unsuspecting Namek village. Frieza wants the fifth Dragon Ball, and he is prepared to learn its location by any means necessary!'),
    (2, 9, 'Namek Saga', 'Escape from Dodoria', 'Gohan risks his life to rescue a Namek boy from the clutches of Frieza’s evil henchmen. Now Gohan and Krillin have an even bigger problem on their hands: Dodoria is chasing them, and he won’t stop until he has his revenge!'),
    (2, 10, 'Namek Saga', 'Secrets Revealed', 'Dodoria’s search for Krillin and Gohan brings him face to face with an unexpected foe – Vegeta! The Saiyan prince has a score to settle with Dodoria, and the time for a final showdown between these two powerful villains has arrived!'),
    (2, 11, 'Namek Saga', 'A Collision Course', 'Goku’s journey to Namek takes an unexpected detour when his spaceship is knocked off course by an asteroid! Goku has to act fast to get his ship back on track because he’s headed straight for the fiery center of a star!'),
    (2, 12, 'Namek Saga', 'Vegeta Has a Ball', 'With his new abilities, Vegeta quickly tracks down and forcefully acquires another Dragon Ball. Now, there is only one magic orb left to find, and Dende knows who has it – the Eldest Namekian!'),
    (2, 13, 'Namek Saga', 'The Past and Future', 'King Kai becomes concerned after learning that Goku is on a collision course with the ruthless Frieza. Meanwhile, back on Planet Namek, the battle between Vegeta and Zarbon has begun!'),
    (2, 14, 'Namek Saga', 'Zarbon Transformed', 'Vegeta’s latest battle heats up as Zarbon reveals his true power: the ability to transform into a monstrous beast! With his increased size and strength, Zarbon seems ready to turn the lights out on the Saiyan Prince – permanently!'),
    (2, 15, 'Namek Saga', 'The Eldest Namek', 'When Krillin speaks to the Eldest Namekian, he gets a double surprise! Not only does he receive a Dragon Ball, but the sleeping powers within him are awoken! Will Krillin’s incredible new strength be enough to save his friends?'),
    (2, 16, 'Namek Saga', 'Get Vegeta!', 'Yamcha, Tien, and Chiaotzu continue training, but their workout gets intense when Piccolo challenges them all to a three-on-one bout! Back on Namek, Frieza’s henchmen try to revive Vegeta in order to obtain the missing Dragon Ball.'),
    (2, 17, 'Namek Saga', 'Vegeta Revived', 'Vegeta escapes from the clutches of Frieza, and steals the Dragon Balls in the process! Elsewhere, Goku’s journey through space grows perilous as his ship is caught in a powerful magnetic storm!'),
    (2, 18, 'Namek Saga', 'A Heavy Burden', 'Krillin returns from his meeting with the Eldest Namekian only to be greeted by a pair of unwelcome visitors: Vegeta and Zarbon! Meanwhile, Gohan discovers the seventh and final Dragon Ball!'),
    (2, 19, 'Namek Saga', 'Immortality Denied', 'The Ginyu Force has been dispatched to Planet Namek to help search for the Dragon Balls. Unaware of this new threat, Krillin and Gohan struggle to keep the seventh Dragon Ball from falling into Vegeta’s evil hands.'),
    (2, 20, 'Namek Saga', 'Big Trouble for Bulma', 'While Krillin and Gohan visit the Eldest Namekian, they leave the seventh Dragon Ball their hidden camp. When the Dragon Ball mysteriously disappears, Bulma must embark on a daring underwater adventure to get it back!'),
    (2, 21, 'Namek Saga', 'Scramble for the Dragon Balls!', 'Bulma is taken hostage by Frieza’s evil henchmen, who force her to lead them on an underwater quest for the Dragon Balls. Without Gohan and Krillin to save her, she’ll have to outsmart her captors – or wind up sleeping with the fishes!'),
    (2, 22, 'Namek Saga', 'Arrival of the Ginyu Force', 'Krillin and Gohan complete their journey to Guru’s house, but little do they know, Vegeta is hot on their trail! Can Guru unlock Gohan’s hidden powers in time to hold off the rampaging Saiyan’s wrath?'),
    (2, 23, 'Namek Saga', 'Elite Fighters of the Universe... The Ginyu Force', 'The Ginyu Force has arrived on Planet Namek! Now, Vegeta, Krillin, and Gohan must form an uneasy alliance as they stand face to face with five of the fiercest warriors in the universe!'),
    (2, 24, 'Namek Saga', 'Time Tricks and Body Binds', 'The battle with the Ginyu Force begins, as Gohan and Krillin launch a barrage of explosive energy blasts at Guldo! The Heroes are rendered helpless by Guldo’s Mind Blind technique, and this time, there is no one to save them!'),
    (2, 25, 'Namek Saga', 'No Refuge From Recoome', 'The battle with Guldo may be over, but the real nightmare is just beginning! Recoome, the most massive member of the Ginyu Force, is ready to fight, and even the mighty Vegeta’s attacks have no effect on this monstrous foe!'),
    (2, 26, 'Namek Saga', 'Enter Goku', 'With Krillin and Vegeta both out of commission, only Gohan remains to carry on the fight against Recoome! The young Saiyan must summon every ounce of his strength and courage in order to face this powerful foe.'),
    (2, 27, 'Namek Saga', "Goku's New Power", 'Goku has arrived on Planet Namek, and without a second to lose! Gohan and Krillin are hanging by a thread, held at the mercy of the Ginyu Force! Has Goku’s training in 100-times gravity prepared him to face these powerful foes?'),
    (2, 28, 'Namek Saga', 'A Legend Revealed', 'As Vegeta, Krillin, and Gohan look on, Goku easily deflects the attacks of Jeice and Burter, two of the Force’s fiercest warriors. Could Goku have become what Vegeta thought was only a legend: a Super Saiyan?'),
    (2, 29, 'Namek Saga', 'Ginyu Assault', 'When Goku proves too much for Burter and Jeice to handle on their own, Jeice retreats in search of reinforcements. Now, the real test for Goku and his newly-acquired powers is about to begin as Captain Ginyu enters the fight!'),
    (2, 30, 'Namek Saga', 'Incredible Force!', 'As the battle between Goku and Captain Ginyu rages on, Gohan and Krillin steal the unguarded Dragon Balls from Frieza’s ship. It’s a race against time, and our heroes must unlock the power of the Dragon Balls before it’s too late!'),
    (2, 31, 'Namek Saga', 'Frieza Approaches', 'Goku astounds Captain Ginyu with his amazing new powers, but the Captain still has a few tricks up his sleeve! Meanwhile, Frieza arrives at the home of the Eldest Namek and begins a battle with the noble warrior, Nail!'),
    (2, 32, 'Namek Saga', 'Goku is Ginyu and Ginyu is Goku', 'In an attempt to save the Elder, Nail fights a hopeless battle against the ruthless Frieza. Meanwhile, finding himself no match for Goku’s superior abilities, Captain Ginyu unleashes his ultimate attack, the Body Switch Technique!'),
    (2, 33, 'Namek Saga', 'Calling the Eternal Dragon', 'Armed with the Dragon Radar, Gohan and Krillin recover the seven Dragon Balls from their hiding places. But before they can summon the Eternal Dragon to make their wish, they are confronted by a powerful new enemy – Goku?!'),
    (2, 34, 'Namek Saga', 'Gohan, Defeat Your Dad!', 'After taking control of Goku’s body, Captain Ginyu turns his attention to Gohan and Krillin! With Goku trapped in the Captain’s broken body, it’s up to Gohan to stop the rampaging Ginyu!'),
    (2, 35, 'Namek Saga', 'Captain Ginyu... The Frog', 'As the bout between Captain Ginyu and Vegeta heats up, Goku summons the last of his strength and tricks his foe into reversing the Body Switch Technique. Now, Goku, Krillin, and Gohan must join forces with Vegeta for the battle with Frieza.'),
    (3, 1, 'Frieza Saga', 'Password is Porunga', 'Having acquired all seven Namekian Dragon Balls, Krillin and Gohan are ready to summon the dragon and make their wish. There’s just one problem: they don’t know the password!'),
    (3, 2, 'Frieza Saga', "Piccolo's Return", 'With the help of young Dende, Krillin and Gohan learn they will be granted three wishes! But even as Krillin and Gohan call upon the dragon, Vegeta races to the scene on a mission to wish for mortality!'),
    (3, 3, 'Frieza Saga', 'The Fusion', 'With the Dragon Balls gone and his plan in ruins, Frieza unleashes his fury upon Vegeta, Gohan, and Krillin. Elsewhere, the newly-revived Piccolo finds himself on Planet Namek. Will his arrival be enough to turn the tide?'),
    (3, 4, 'Frieza Saga', 'Fighting Power: One Million?', 'Frieza reveals a dark secret from Vegeta’s past, but the villain has an even more shocking secret in store for the Z-fighters! As the monster’s power level rises to terrifying new heights, all hope for the universe seems lost!'),
    (3, 5, 'Frieza Saga', 'Gohan Attacks', 'Frieza claims his first victim, Krillin, and Gohan must summon every ounce of his strength in order to save his friend. Can the young Saiyan put a stop to Freiza’s ruthless onslaught, or is he destined to become the next victim?'),
    (3, 6, 'Frieza Saga', 'Piccolo the Super-Namek', 'Gohan and Krillin continue their struggle against the overwhelming powers of Frieza, but as the fighting reaches its peak, a new warrior arrives on the battlefield to aid them in their efforts!'),
    (3, 7, 'Frieza Saga', 'Deja Vu', 'Piccolo quickly takes control of the battle with Frieza, and the putrid purple monster is shocked to learn the secret behind his opponent’s powers!'),
    (3, 8, 'Frieza Saga', "Frieza's Second Transformation", 'Just as it appears that Piccolo has gained the upper hand, Frieza quickly dashes all hopes for victory by revealing his second monstrous transformation!'),
    (3, 9, 'Frieza Saga', 'Another Transformation?', 'Unable to watch as Piccolo is overwhelmed by Frieza, Gohan springs into action! Meanwhile, Vegeta devises a risky plan for transforming himself into a Super Saiyan!'),
    (3, 10, 'Frieza Saga', "Dende's Demise", 'Having reached his ultimate form, Frieza is determined to destroy the remaining Z-fighters one by one, but Vegeta boldly announces the end of Frieza’s tyrannical reign! Are Vegeta’s claims true? Has he become a Super Saiyan?'),
    (3, 11, 'Frieza Saga', 'The Renewed Goku', 'Despite his new powers, Vegeta proves no match for Frieza! Meanwhile, Goku’s time in the rejuvenation chamber is nearly complete! Can he reach the battlefield in time to save his friends?'),
    (3, 12, 'Frieza Saga', 'The End of Vegeta', 'Goku rejoins his friends on the battlefield, but not before Vegeta is defeated by Frieza! As the Saiyan Prince clings to life by a thread, he reveals the secrets of his violent past.'),
    (3, 13, 'Frieza Saga', 'The Ultimate Battle', 'Feeling a new sense of connection to the dwindling Saiyan race, Goku wages war on the monstrous Frieza! As the fight intensifies, Frieza directs his energy blasts at Namek itself, turning the planet into a lava-spewing war zone!'),
    (3, 14, 'Frieza Saga', 'Clash of the Super Powers', "Goku and Frieza continue their epic battle! An underwater attack puts Goku on top until Frieza traps him in an energy ball! It's fun and games for Frieza, but the exploding ball may prove deadly for Goku!"),
    (3, 15, 'Frieza Saga', "Frieza's Boast", 'Frieza vows to beat Goku without using his hands, but the mighty Saiyan soon makes the mosnter eat his words! Elsewhere, Captain Ginyu uses his Body Switch Technique on Bulma, leaving her trapped in the body of a frog!'),
    (3, 16, 'Frieza Saga', 'Bold and Fearless', "Captain Ginyu returns to the battlefield in Bulma's body! Can Piccolo, Krillin, and Gohan handle this Femme Fatale? Later, Frieza powers up to fifty percent of his maximum, and Goku finds himself completely outmatched!"),
    (3, 17, 'Frieza Saga', 'Embodiment of Fire', 'Goku’s powerful Kaio-Ken attack has no effect on Frieza, who is still only fighting with fifty-percent of his power! Just as it seems Frieza has won the battle, a dream-like vision helps Goku ascend to a higher level of power and strength!'),
    (3, 18, 'Frieza Saga', 'Trump Card', 'Once again, Goku is rescued by a vision! This time, Vegeta talks to Goku from beyond the grave to offer new hope and encouragement! But when Goku realizes that the battle against Frieza is futile, he turns to his last resort: the Spirit Bomb!'),
    (3, 19, 'Frieza Saga', 'Keep the Chance Alive!!', 'Yamcha, Tien, and Chiaotzu find themselves in serious trouble when the Ginyu Force invades King Kai’s planet! Meanwhile, as Frieza thwarts Goku’s efforts to gather energy for the Spirit Bomb, Piccolo must enter the battle!'),
    (3, 20, 'Frieza Saga', 'Power of the Spirit', 'Chaos erupts on King Kai’s planet as the Z-fighters battle the Ginyu Force! Back on Planet Namek, the life and death struggle between Piccolo and Frieza rages on, and Goku completes his Spirit Bomb!'),
    (3, 21, 'Frieza Saga', 'Transformed at Last', 'A victory celebration comes to a halt when Frieza reappears! With no reserves left, Goku watches helplessly as Frieza directs his fury at Piccolo and Krillin. Enraged by the loss of his friends, Goku undergoes a wild transformation!'),
    (3, 22, 'Frieza Saga', 'Explosion of Anger', 'Engulfed in golden light, Goku announces that he is now a Super Saiyan! Frieza is unimpressed – until the fighting begins! In a raging battle, Frieza is horrified when he realizes that Goku is now superior to him in every way!'),
    (3, 23, 'Frieza Saga', "Namek's Destruction?", 'Finding himself no match for Goku, Frieza attacks Planet Namek! Unable to react in time, Goku is forced to watch helplessly as the fiery blast rips through Namek’s core! Can anyone survive such incredible destruction?'),
    (3, 24, 'Frieza Saga', 'A Final Attack', 'With only minutes to go before the planet explodes, Frieza reaches his maximum power! Meanwhile, Gohan and Bulma race back to Goku’s spaceship. Can Goku defeat Frieza in time to rejoin his son and fly to safety?'),
    (3, 25, 'Frieza Saga', 'Approaching Destruction', 'The battle between Goku and Frieza rages on! Back on Earth, the seven Dragon Balls have been restored, but with Namek’s destruction imminent, can Kami and Mr. Popo summon the Eternal Dragon before it’s too late?'),
    (3, 26, 'Frieza Saga', 'Gohan Returns', 'Frieza’s victims have been wished back to life, but as they begin to rise, Goku falls – overwhelmed by Frieza’s devastating assault. Sensing his father’s defeat, Gohan rushes to the scene as the universe’s final hope.'),
    (3, 27, 'Frieza Saga', 'The Last Wish', 'Guru and the people of Namek have been brought back to life, and the dragon Porunga has reappeared to grant the last of three wishes. While a newly enraged Goku resumes his onslaught against the evil Frieza, Dende races to make the final wish!'),
    (3, 28, 'Frieza Saga', 'Duel on a Vanishing Planet', 'Goku chooses to stay behind and finish his fight with Frieza. With Namek set to explode any second, there seems no way for Goku to defeat Frieza and escape in time! Has the Super Saiyan made the greatest mistake of his life?'),
    (3, 29, 'Frieza Saga', 'Pathos of Frieza', 'Time grows short for Goku as each passing second brings Namek closer to ultimate destruction. As the Super Saiyan’s strength increases with every blow, it appears his epic battle with Frieza has at last reached its conclusion!'),
    (3, 30, 'Frieza Saga', 'Frieza Defeated!!', 'Frieza lashes out in a blind rage, launching a reckless volley of energy attacks. In the face of Goku’s superior power, the evil tyrant’s greatest fear has finally been realized: defeat at the hands of a Super Saiyan!'),
    (3, 31, 'Frieza Saga', 'Mighty Blast of Rage', 'Even after being sliced into pieces by his own energy disk, Frieza isn’t ready to release his stranglehold on the universe. With what little power he has left, Frieza fires a final energy blast after Goku as he leaves the battlefield!'),
    (3, 32, 'Frieza Saga', "Namek's Explosion... Goku's End?", 'Even though it looks like Goku is trapped on the exploding planet Namek, Dende has a good reason to celebrate: the Dragon Balls have the power to bring Goku back! But if that’s the case, why does everyone still look so sad?'),
    (3, 33, 'Frieza Saga', "Goku's Alive!!", 'It is a time of joyful reunions as old friends long absent are finally wished home with the Dragon Balls! Krillin and Yamcha are brought back from the spirit world, but Porunga, the Namekian dragon, has startling news about Goku!'),
    (4, 1, 'Androids Saga', 'The Heavens Tremble', "Gohan's going fishing, Krillin's found a girlfriend, and it looks as though peace has once again returned to the Earth. But a terrible evil lurks beneath this tranquil surface: Garlic Junior has escaped from the Dead Zone!"),
    (4, 2, 'Androids Saga', 'Black Fog of Terror', "With the help of the Spice Boys, Garlic Junior releases the Black Water Mist upon an unsuspecting world. As the dreaded fog spreads, so does Garlic Junior's control over the Earth!"),
    (4, 3, 'Androids Saga', "Battle in Kami's Lookout", 'As Piccolo attempts to hold off the Spice Boys and the infected Z Fighters, Gohan and Krillin race toward Kami’s Lookout to retrieve the one thing capable of reversing the effects of the Black Water Mist: the Sacred Water!'),
    (4, 4, 'Androids Saga', 'Fight with Piccolo', 'With Piccolo infected by the Black Water Mist and Kami trapped in a glass bottle, Garlic Jr. allows his Spice Boys to “have sport” with Earth’s heroic defenders. Will Spice’s energy blast finish off Krillin for good?'),
    (4, 5, 'Androids Saga', 'Call for Restoration', 'Krillin, after suffering a Spice Boys beating, attempts to free Kami and Mr. Popo, but he soon falls prey to the Black Water Mist. Gohan is the only hero left who can save the Earth, but can he do it with his two best friends against him?'),
    (4, 6, 'Androids Saga', 'Suicidal Course', 'Piccolo and Krillin spring their trap, revealing that they have pretended to be infected by the Black Water Mist! Enraged, Garlic Jr. transforms using the energy of the Makyo Star and warns that the Sacred Water’s effectiveness will soon expire.'),
    (4, 7, 'Androids Saga', 'Extreme Measures', 'Garlic Junior and his Spice Boys harness the evil power of the Makyo Star to become stronger than ever, but Gohan, Krillin, and Piccolo are ready to battle this new threat!'),
    (4, 8, 'Androids Saga', 'The World Awakens', 'In a last ditch effort to save his friends, Gohan launches an all out assault on Garlic Junior! Meanwhile, deep within the Lookout, Kami and Mr. Popo are under siege by the Former Guardians!'),
    (4, 9, 'Androids Saga', 'Brief Chance for Victory', 'Blinded by rage and desperate to destroy his enemies, Garlic Junior uses his power to open up the Dead Zone! With Piccolo and Krillin out of commission, Gohan is the only one left who can stop him!'),
    (4, 10, 'Androids Saga', "Krillin's Proposal", 'Even though peace has been restored on Earth, Krillin faces his toughest challenge ever: surviving a shopping trip with Maron! And it looks like she’s picking out a wedding dress! Are Krillin and Maron planning to tie the knot?'),
    (4, 11, 'Androids Saga', "Frieza's Counterattack", 'Gohan’s cracking the books, and his new tutor is cracking the whip! But study time is almost over, for a powerful evil is racing toward the Earth! Gohan’s worst fears have come to life: Frieza has survived!'),
    (4, 12, 'Androids Saga', 'The Mysterious Youth', 'The Earth faces its darkest hour as Frieza and his father King Cold rapidly approach! Without Goku to assist them, the Z-Fighters prepare to launch a desperate attack against the most powerful evil the universe has ever known!'),
    (4, 13, 'Androids Saga', 'Another Super Saiyan?', 'Frieza and King Cold descend upon the Earth, but a mysterious warrior has come to thwart their diabolical plot for revenge. Does this brash young hero have what it takes to stand up to these twin titans of evil?'),
    (4, 14, 'Androids Saga', 'Welcome Back Goku', "After defeating Frieza and King Cold, the mysterious stranger announces the exact time and place of Goku's arrival on Earth. Can this young Super-Saiyan really predict the future?! Gohan and the others are determined to find out!"),
    (4, 15, 'Androids Saga', 'Mystery Revealed', 'After testing Goku in combat, the mysterious stranger reveals his true identity! What does his timely arrival mean?! In a startling conversation with Goku, this powerful hero from the future tells all!'),
    (4, 16, 'Androids Saga', "Goku's Special Technique", 'The future has been written – or has it? That’s what Goku and the rest of the Z-Fighters must decide as they hear Trunks’ ominous warning. The Androids are coming! And they just might be bringing the end of the world with them!'),
    (4, 17, 'Androids Saga', 'Z Warriors Prepare', 'Gohan learns some new tricks, Vegeta pushes himself to the breaking point, and Yamcha struggles just to keep up as everyone prepares to face the looming Android menace! But will all their preparations be enough?'),
    (4, 18, 'Androids Saga', "Goku's Ordeal", 'ChiChi wants a car! Goku and Piccolo take a day off from training to enroll in driving school. These two mighty warriors may be the Earth’s only chance for survival, but what are the chances they’ll learn how to parallel park?'),
    (4, 19, 'Androids Saga', 'The Androids Appear', 'Three years have come and gone, and the day of reckoning has finally arrived! The Androids are here, and they’re wreaking havoc on an unsuspecting city! Goku and his friends must now put their training to the test!'),
    (4, 20, 'Androids Saga', 'A Handy Trick', 'Yamcha is held at the mercy of the ruthless Android 20, and Goku and the others must race to help their friend. Believing their power to be far superior, the Androids tempt Goku’s rage by leveling half of the city!'),
    (4, 21, 'Androids Saga', 'Double Trouble for Goku', 'The battle with the Androids begins as Goku launches an all out assault against Android 19. The Super Saiyan seems to have the fight under control, but something is about to go horribly wrong!'),
    (4, 22, 'Androids Saga', 'Upgrade to Super Saiyan', 'Attacked from within by a crippling virus, Goku is helpless against the maniacal Android 19. But just when it looks like the end for Goku, Vegeta appears on the scene! And he’s got a few big surprises in store for the Androids!'),
    (4, 23, 'Androids Saga', 'The Secret of Dr. Gero', 'In his first fight as a Super Saiyan, Vegeta takes control of the battlefield and defeats Android 19 in convincing fashion! Unwilling to share 19’s fate, Android 20 runs for cover in the mountains!'),
    (4, 24, 'Androids Saga', 'More Androids?!', 'Vegeta, Piccolo, and Gohan lead an exhaustive search through the mountains for Android 20. But the hunters are also the hunted! Android 20 lurks in the shadows, ready to strike, and it looks like Piccolo is his first target!'),
    (4, 25, 'Androids Saga', 'Follow Dr. Gero', 'Our heroes make a startling discovery: Android 20 is none other than Dr. Gero himself! Before they can act on this new knowledge, the diabolical doctor flees to his secret laboratory, where he intends to awaken more killer androids!'),
    (4, 26, 'Androids Saga', 'Nightmare Comes True', 'The race is on, as the Z-Fighters search frantically for Dr. Gero’s hidden laboratory! But rather than stop the androids before they’re activated, Vegeta wants a challenge! Despite Trunks’ warning, he chooses to fight the androids alone'),
    (4, 27, 'Androids Saga', "Goku's Assassin", 'Dr. Gero escapes to his mountain hideout and brings his killer androids to life. Without the help of Goku, all hope seems lost. Dr. Gero appears one step closer to ultimate vengeance, but his evil creations have a vendetta of their own!'),
    (4, 28, 'Androids Saga', 'Deadly Beauty', 'Vegeta and Android 18 have a showdown on the highway. Trunks and the others are there to help, but the Saiyan prince insists on fighting his opponent man-to-android! Will Vegeta’s overconfidence be his undoing?'),
    (4, 29, 'Androids Saga', 'No Match for the Androids', 'In an earthshaking battle, the beautiful Android 18 brings Vegeta to his knees. But before she can deliver the final blow, Trunks steps in to help. Soon an all out war between good and evil begins, and the androids have the upper hand.'),
    (4, 30, 'Androids Saga', 'Last Ditch Effort', 'Vegeta, Trunks, Tien, and Piccolo realize a grim truth: unless they can increase their powers quickly, they’ll have no chance against the androids. In a drastic move, Piccolo flies to Kami’s Lookout and makes a most unexpected proposal!'),
    (4, 31, 'Androids Saga', 'Closing In', 'The androids hit the road in pursuit of Goku, but they’re delayed by some hyperactive hoodlums. Krillin and Trunks race to move Goku to a safer hiding place, and Kami wrestles with Piccolo’s difficult offer.'),
    (4, 32, 'Androids Saga', 'Unwelcome Discovery', 'The Z-fighters retreat to Master Roshi’s house to plan their next move. Meanwhile, Bulma makes a startling discovery: the wreckage of a second time capsule! Where did it come from, and more importantly, who was in it?'),
    (5, 1, 'Cell Saga', 'Seized with Fear', 'Trunks and Krillin join Bulma at the crash site of the mysterious time capsule and find an eerie clue: the shell of a large, locust-like creature! Whatever arrived in the time capsule isn’t human, and it’s on the loose!'),
    (5, 2, 'Cell Saga', 'The Reunion', 'An insect-like monster threatens to turn Gingertown into a ghastly graveyard! In response to this new menace, Kami fuses with Piccolo, and the resulting Super Namekian flies to Gingertown for a showdown of epic proportions!'),
    (5, 3, 'Cell Saga', 'Borrowed Powers', 'Gingertown becomes a battlefield as Piccolo confronts Cell. This monster from the future gains his strength by sucking the life out of his victims! But that’s not the creature’s only talent. He also knows the Kamehameha Wave!'),
    (5, 4, 'Cell Saga', 'His Name is Cell', 'Heavily-armored tanks fail to halt Cell’s rampage, and now it’s up to Piccolo to stop the monster! As the Namekian fights for survival, Cell reveals that he’s actually an android, the ultimate achievement of Dr. Gero!'),
    (5, 5, 'Cell Saga', "Piccolo's Folly", 'Piccolo cleverly distracts Cell long enough to regenerate his arm. The Namekian is ready for another round, and Krillin and Trunks have arrived to provide backup! With the odds mounting against him, Cell makes a tactical decision.'),
    (5, 6, 'Cell Saga', 'Laboratory Basement', 'With hopes of saving the future, Trunks and Krillin race to destroy Dr. Gero’s lab. Meanwhile, Piccolo and Tien search for the elusive Cell. But how can they stop an enemy who knows their every move?'),
    (5, 7, 'Cell Saga', 'Our Hero Awakes', 'In South City, Cell plows through more civilians and accidentally runs into Krillin! Goku finally gets back on his feet, but with Cell and the other androids in full stride, can the Saiyan hero still make a difference?'),
    (5, 8, 'Cell Saga', 'Time Chamber', 'As Cell continues his deadly march, Goku hatches a plan to squeeze a year’s worth of training into just one day! Back at Master Roshi’s, the android trio arrives looking for Goku! Can Piccolo hold them off until the Saiyans return?'),
    (5, 9, 'Cell Saga', 'The Monster is Coming', 'Behind the closed doors of the Hyperbolic Time Chamber, Vegeta and Trunks struggle to push past the level of Super Saiyan! Down on Earth, Piccolo challenges Android 17 to a battle!'),
    (5, 10, 'Cell Saga', "He's Here", 'Stronger than ever after fusing with Kami, Piccolo leads the attack against the androids! It looks like the Super Namekian has things under control until Cell arrives on the battlefield! Can anyone stop this hideous monster?!'),
    (5, 11, 'Cell Saga', 'Up to Piccolo', 'Just as Cell is about to absorb Android 17, Piccolo bravely steps in and foils the monster’s plan! Does the Super Namekian really have a chance at stopping Cell on his own?! Or is he simply putting off the inevitable?'),
    (5, 12, 'Cell Saga', 'Silent Warrior', 'When Android 16 claims to be as strong as Cell, it seems like a wild boast! But after he launches an offensive that throws Cell against the ropes, it becomes clear that the big android has the power to back up his words!'),
    (5, 13, 'Cell Saga', 'Say Goodbye, 17', 'It’s android against android as 16 clashes with Cell. Android 16 is the stronger fighter, but Cell is far too driven to be stopped now! With an underhanded attack, Cell moves one step closer to his gruesome transformation!'),
    (5, 14, 'Cell Saga', 'Sacrifice', 'With an onslaught of psychic blasts, Tien gives Androids 16 and 18 a chance to escape, but the powerful attack rapidly drains his strength. Tien may have saved the androids, but can he save himself?'),
    (5, 15, 'Cell Saga', 'Saiyans Emerge', 'Trunks and Vegeta emerge from the time chamber after a year of intense training. Goku and Gohan are next into the room, but with Cell nearing his ultimate form, can the fighters afford to wait another day?'),
    (5, 16, 'Cell Saga', 'Super Vegeta', 'Cell obliterates a chain of islands in search of Android 18! Vegeta, fresh from the time chamber, is ready to test his new strength against the monster, but is he really stronger than a Super Saiyan?'),
    (5, 17, 'Cell Saga', 'Bow to the Prince', 'It’s show-and-tell for Vegeta as he demonstrates how much difference a year of training can make! Meanwhile, back in the time chamber, Gohan struggles to become a Super Saiyan.'),
    (5, 18, 'Cell Saga', 'Hour of Temptation', 'Vegeta quickly pounds Cell six feet into the ground! With his back against the wall, the monstrous android attacks Vegeta’s weakest point: his arrogance! Can the Saiyan Prince resist Cell’s tempting challenge?'),
    (5, 19, 'Cell Saga', "Krillin's Decision", 'With beautiful Android 18 in his sights, Krillin clutches the controller that will shut her down forever. But when the moment arrives, the little man hesitates! All the while, Cell looms overhead, hungry for perfection!'),
    (5, 20, 'Cell Saga', 'The Last Defense', 'With the remote control smashed, Krillin and Trunks must save Android 18 from Cell’s power-hungry grasp. But Vegeta has other plans in mind. Will trunks attack his own father to save humanity?'),
    (5, 21, 'Cell Saga', 'Cell is Complete', 'The earth’s greatest fear has come true: Cell is complete! Can anyone stop the android nightmare in his final, perfect form? As the heroes nervously line up, a glimmer of hope shines from above. Gohan is a Super Saiyan!'),
    (5, 22, 'Cell Saga', 'Vegeta Must Pay', 'After allowing Cell to reach his final form, Vegeta is ready for the challenge he was promised. But as Cell easily deflects the Saiyan’s every blow, it’s clear that Vegeta has more on his hands than he bargained for!'),
    (5, 23, 'Cell Saga', 'Trunks Ascends', 'Tapping into the deepest wells of his energy, Vegeta summons one last attack: the Final Flash! Meanwhile, Trunks struggles to decide whether or not to help his father. Vegeta’s pride is at stake, but so is his life!'),
    (5, 24, 'Cell Saga', 'Saving Throw', 'Vegeta lies unconscious after his battle with Cell, and Trunks unleashes his hidden powers to save his father’s life. With Goku and Gohan still training, Trunks is the only person standing in the evil android’s way.'),
    (5, 25, 'Cell Saga', 'Ghosts from Tomorrow', 'Trunks vows to stop the future from repeating itself; Cell can’t wait for the future to unfold. It’s all up for grabs as the two warriors prepare for battle. Only one future will survive. Whose will it be?'),
    (5, 26, 'Cell Saga', 'The Cell Games', 'Realizing that his powers are no match for his opponent, Trunks accepts defeat, only to be given a second chance when Cell proposes a tournament! Is Cell really interested in competition, or does he have a sinister motive?'),
    (6, 1, 'Cell Games Saga', 'What is the Tournament?', 'While Trunks tells the others of Cell’s plans to hold a tournament, the diabolical android begins his preparations for the competition by constructing a fighting arena. Do the Z-Fighters have a chance, or is this a contest that only Cell can win?'),
    (6, 2, 'Cell Games Saga', 'The Doomsday Broadcast', 'Cell breaks into showbiz, literally! The sinister android hijacks a television station in order to announce his "Cell Games" to the world! But are there any challengers left with the strength and courage to get into the ring?'),
    (6, 3, 'Cell Games Saga', 'Meet Me in the Ring', 'Panicked Earthlings flee their homes to escape Cell’s wrath, but all hope is not lost! Back at the Lookout, Goku and Gohan finally emerge from the Time Chamber. After a quick trip to size up the competition, Goku is ready to battle Cell!'),
    (6, 4, 'Cell Games Saga', 'No Worries Here', "With nine days until Cell's tournament begins, Vegeta, Piccolo, and Trunks plan to return to the Hyperbolic Time Chamber. But Goku decides that he and Gohan have had enough training! What does Goku know that the others don't?"),
    (6, 5, 'Cell Games Saga', 'A Girl Named Lime', "Gohan stumbles upon a village that has retreated to a nearby shelter, and when he discovers that the owner of the shelter is capitalizing on the villagers' fear of Cell, he comes up with a Super Saiyan solution to the problem!"),
    (6, 6, 'Cell Games Saga', 'Memories of Gohan', "As the Cell Games draw near, Goku enjoys his remaining time with friends and family! First he fishes with Krillin, then he strolls down memory lane with Chichi, and finally it's time for a very special boy to blow out the candles!"),
    (6, 7, 'Cell Games Saga', 'A New Guardian', 'When the Royal Military foolishly tries to stop Cell with ordinary weapons, the attack quickly becomes a suicide mission! Goku is determined to revive the fallen soldiers, but that will require new Dragon Balls!'),
    (6, 8, 'Cell Games Saga', "Dende's Dragon", 'With help from King Kai, Goku travels to Namek to recruit a new guardian for the Earth! Most of the Namekians refuse the offer, but there’s one little guy who can’t wait to go! Dende is back, and he’s going to create a new Dragon!'),
    (6, 9, 'Cell Games Saga', 'The Puzzle of General Tao', 'Goku comes face to face with an old adversary: General Tao! The search for the Dragon Balls led Goku to the aging general, but unless the Super Saiyan can solve the crafty villain’s puzzle, the search may end in vain!'),
    (6, 10, 'Cell Games Saga', 'The Games Begin', 'The wait is over, and the Cell Games are ready to begin! The Z-Fighters arrive ringside, only to discover another challenger already on the scene. It’s none other than World Martial Arts Champion, Mr. Satan!'),
    (6, 11, 'Cell Games Saga', 'Losers Fight First', 'Caroni and Pirozhki, Mr. Satan’s top students, make a spectacular entrance to the ring, but are they really ready to rumble with Cell? Don’t miss a minute of the fun, because this fight could be over fast!'),
    (6, 12, 'Cell Games Saga', 'Goku vs. Cell', 'The main event begins! Now free of distraction, Goku steps into the ring to face Cell. The Earth shakes and the heavens tremble as these mighty super warriors collide! And that’s just the warm up!'),
    (6, 13, 'Cell Games Saga', "Cell's Bag of Tricks", 'Cell attacks Goku with a dazzling array of moves: the Destructo Disk, the Special Beam Cannon, even the Kamehameha Wave! So far, Goku has been able to match Cell blow for blow, but how will the Super Saiyan fare against such a lethal arsenal?'),
    (6, 14, 'Cell Games Saga', 'No More Rules', 'As the battle intensifies, Cell quickly grows tired of the rules he created for the tournament. With a flick of his finger, the Android destroys the ring, instantly turning the Cell Games into a deadly fight to the finish!'),
    (6, 15, 'Cell Games Saga', 'The Fight is Over', 'Goku blasts Cell with a Kamehameha Wave that reduces the android to a pile of cinders, but his triumph is short-lived. The monster shows his amazing resilience by fully regenerating himself!'),
    (6, 16, 'Cell Games Saga', 'Faith in a Boy', 'After surrendering to Cell, Goku names the next challenger to enter the Cell Games: Gohan! Goku has supreme faith in his son’s abilities, but the young Saiyan will need a lot more than his father’s confidence if he’s going to survive!'),
    (6, 17, 'Cell Games Saga', "Gohan's Desperate Plea", 'The fight between Gohan and Cell intensifies, but the villain’s attacks seem to have no effect on the boy! Could the young hero really have the power to defeat the evil android once and for all?'),
    (6, 18, 'Cell Games Saga', 'Android Explosion', 'Cell is determined to unleash Gohan’s full potential, but the boy refuses to fight, prompting the android to torture Gohan’s friends instead! Next, Cell does the unthinkable by spawning miniature Cells to attack the Z-Fighters!'),
    (6, 19, 'Cell Games Saga', 'Cell Juniors Attack!', 'Gohan boils with rage as the Cell Juniors wreak havoc on the Z-Fighters. The boy struggles to resist the urge to fight, but he’s a powder keg waiting to explode, and Android 16 appears ready to light the fuse!'),
    (6, 20, 'Cell Games Saga', 'The Unleashing', 'Spurred by Android 16’s dying words, Gohan’s hidden power is finally unleashed! With his new strength and speed, Gohan easily destroys the wicked Cell Juniors, but his sights are set on a bigger target!'),
    (6, 21, 'Cell Games Saga', 'The Unstoppable Gohan', 'Cell’s desire for battle turns into a nightmare as Gohan unleashes the full fury of his strength. The evil android powers up to his maximum level, but will it be enough to spare him from the wrath of Super Saiyan?'),
    (6, 22, 'Cell Games Saga', "Cell's Mighty Breakdown", 'Gohan’s Super Saiyan strength appears to have no limit, and the young hero delivers a blow so severe it causes Cell to cough up Android 18! As the monster wears down, Gohan prepares to end the battle once and for all!'),
    (6, 23, 'Cell Games Saga', "A Hero's Farewell", 'Clearly overmatched by Gohan, Cell initiates his last line of defense: a self-destruct program that will blow up the entire planet! With only seconds to spare, Goku risks everything to transport Cell away from the Earth.'),
    (6, 24, 'Cell Games Saga', 'Cell Returns!', 'The nightmare continues! Cell explodes, but a particle of his nucleus survives the blast, providing all the android needs to regenerate himself! Restored to his ultimate form, Cell returns to the Earth more powerful than ever!'),
    (6, 25, 'Cell Games Saga', "The Horror Won't End", 'After easily dispensing of both Trunks and Vegeta, Cell announces a new plan. First, he’ll destroy the Earth, and after that, the Universe will be his next target! Can this weapon of ultimate destruction be stopped?'),
    (6, 26, 'Cell Games Saga', 'Save the World', 'The final showdown begins! While Goku telepathically coaches Gohan from the Other World, the Z-Fighters jump in for a five-sided attack! Gohan has the potential inside him, but can Goku show him how to unlock it?'),
    (6, 27, 'Cell Games Saga', "Goku's Decision", 'Cell is finally defeated, but the Z-Fighters still have much to resolve! Can they make it to the Lookout in time to heal the badly-injured Gohan? Is Android 18 still a threat? And can our heroes find a way to bring back Goku?'),
    (6, 28, 'Cell Games Saga', 'One More Wish', "After Goku’s decision to stay in the after-world, Krillin uses the final wish to save Android 18, but does he have the courage to reveal his true feelings? And is anyone brave enough to break the news of Goku's passing to Chichi?!"),
    (6, 29, 'Cell Games Saga', 'Free the Future', 'Peace and order have been restored on Earth in the present, but Trunks’ future world is still a place of darkness and despair! Once he arrives home, the future will be forever changed!'),
    (7, 1, 'World Tournament Saga', 'Warriors of the Dead', 'When Goku hears about a martial arts master known as the Grand Kai, he rushes to meet him for a lesson! Meanwhile, Cell, Frieza, King Cold and the Ginyu Force have teamed up to take control of Other World!'),
    (7, 2, 'World Tournament Saga', 'Tournament Begins', 'Goku must train for 10,000 years before he can study under the Grand Kai! But when the West, South, and East Kai’s decide to hold an Other World Tournament, Goku gets his chance! All he has to do is defeat the greatest fighters of all time!'),
    (7, 3, 'World Tournament Saga', 'Water Fight', "The Other World Tournament advances to the Quarter-Finals, and the battles are out of this world! Goku's opponent, Arqua, appears to be a wimp, but things change quickly when he transforms the entire ring into water!"),
    (7, 4, 'World Tournament Saga', 'Final Round', "Goku advances to the final round of the tournament where he will face the warrior Pikkon! Sparks of energy fly as the brawlers battle for the title! When Pikkon reveals a Piccolo-like secret, Goku must up the ante! It's Super Saiyan time!"),
    (7, 5, 'World Tournament Saga', 'Goku vs. Pikkon', "Goku may be a Super Saiyan, but can he withstand Pikkon's unbelievable Thunder Flash Attack?! And that's not all! While Goku's been fighting in Other World, seven years have passed on Earth, Gohan is now a teenager!"),
    (7, 6, 'World Tournament Saga', 'Gohan Goes to High School', 'On his first day of high school, Gohan stops a truckload of bank robbers by turning Super Saiyan. Now, the city can\'t stop talking about this mysterious “Gold Fighter!” Can Gohan get through class without revealing his secret identity?'),
    (7, 7, 'World Tournament Saga', 'I am Saiyaman', 'Afraid he’ll be recognized by his classmates, Gohan gets Bulma to design a retractable super-hero costume that he can activate in an instant. Say goodbye to Gohan – and hello to Saiyaman!'),
    (7, 8, 'World Tournament Saga', "Gohan's First Date", "Gohan thinks being a super-hero is a snap until a pretty girl named Angela discovers his secret. When Angela threatens to tell all unless he goes on a date with her, Gohan's life suddenly becomes more complicated than ever!"),
    (7, 9, 'World Tournament Saga', 'Rescue Videl', "When the Red Shark Gang kidnaps the mayor and demands a showdown with Mr. Satan, it's Videl who answers the challenge. Gohan knows Videl is in over her head, but he can't leave his classroom to help her without blowing his cover!"),
    (7, 10, 'World Tournament Saga', 'Blackmail', 'When a greedy circus promoter kidnaps a baby dinosaur, all he sees are dollar signs! Little does he know, that the dinosaur is a close, personal friend of the Great Saiyaman!'),
    (7, 11, 'World Tournament Saga', "I'll Fight Too!", 'Lights! Camera! Action! The Great Saiyaman is about to become a movie star! But the hero’s brush with stardom better not take long, because he has to hurry up and tell all of his old friends the big news: Goku’s coming back!'),
    (7, 12, 'World Tournament Saga', 'The Newest Super Saiyan', 'While training for the upcoming tournament, Gohan discovers that Goten has already reached the level of Super Saiyan! Sparks fly when the brothers spar, but the main event happens when Videl meets Chichi for the first time!'),
    (7, 13, 'World Tournament Saga', 'Take Flight Videl', 'With the Tournament fast approaching, Videl and Goten must learn to fly! Miles away, Vegeta holds a training session of his own, and his young son, Trunks, has a big surprise in store for him'),
    (7, 14, 'World Tournament Saga', 'Gather For the Tournament', "Videl learns to fly, and Gohan and Goten do some last minute honing of their Super Saiyan skills. On the island where the tournament will be held, a special guest arrives! What do you say to a hero who's been dead for seven years?!"),
    (7, 15, 'World Tournament Saga', 'Camera Shy', 'High school jock, Sharpner, discovers his crush, Videl, has her heart set on the mysterious Great Saiyaman! Refusing to be replaced, Sharpner vows to ruin the caped fighter by unmasking his true identity and capturing it on film!'),
    (7, 16, 'World Tournament Saga', 'The World Tournament', 'The action begins as the World Martial Arts Tournament opens with the Junior Division! Thirty-five young fighters vie for the prize, but the matches prove to be more comedy than competition – until Trunks steps into the ring!'),
    (7, 17, 'World Tournament Saga', 'Trunks vs. Goten', "Goten and Trunks breeze through the Junior Division of the tournament until they find themselves going head-to-head in the finals! Who will win this exciting match? This is one championship fight you won't want to miss!"),
    (7, 18, 'World Tournament Saga', 'Best of the Boys', 'The match for the Junior Division World Championship continues as Goten and Trunks battle for the title! The winner of this final joust becomes the new World Champion! Can Goten outwit the cunning Trunks?'),
    (7, 19, 'World Tournament Saga', 'Big Trouble, Little Trunks', "After winning the championship, Trunks fights an exhibition match against Mr. Satan! Can the Champ hold on to his reputation as the world's strongest fighter? Meanwhile, two mysterious figures reveal themselves to Goku!"),
    (7, 20, 'World Tournament Saga', 'Who Will Fight Who?', 'Trunks and Gohan infiltrate the adult competition at the tournament by donning the disguise of Mighty Mask. The pairings for the day’s matches are selected. The first to fight: Krillin vs. Pintar, a man easily ten times Krillin’s size!'),
    (7, 21, 'World Tournament Saga', 'Forfeit of Piccolo!', 'Piccolo stuns the crowd by surrendering to his mysterious opponent before the first punch is thrown! Next into the ring is Videl, who must face the enormous Spopovitch. Will she be able to handle such a large job?'),
    (7, 22, 'World Tournament Saga', 'A Dark and Secret Power', 'Videl takes to the ring for what is expected to be an easy victory over Spopovitch. She hits the towering brute with everything she’s got, but her attacks have no effect. It seems Spopovitch is possessed by a supernatural power!'),
    (7, 23, 'World Tournament Saga', 'Videl is Crushed', 'To everyone’s horror, Spopovitch delays his inevitable victory for the purposes of torturing Videl! It appears the muscle-bound thug isn’t going to stop until he kills her! Will Videl make it out of the ring alive?'),
    (7, 24, 'World Tournament Saga', 'Identities Revealed', 'Gohan’s identity is finally discovered as he takes his place on the tournament floor, but he has bigger things to worry about. His opponent, Kibito, is determined to see him transform into a Super Saiyan!'),
    (7, 25, 'World Tournament Saga', 'Energy Drain', 'When Gohan transforms into a Super Saiyan, Spopovitch and Yamu spring into action! Armed with a mysterious energy-draining device, the pair launch an attack on the golden-haired teen.'),
    (8, 1, 'Majin Buu Saga', "The Wizard's Curse", 'The Z-Fighters race to stop Babidi’s cronies from delivering the pure energy that will be used resurrect the dreaded Majin Buu. Will they find Babidi’s hidden spaceship in time?'),
    (8, 2, 'Majin Buu Saga', 'King of the Demons', 'Piccolo and Krillin are turned to stone by Dabura! Determined to save their friends, Goku, Gohan, and Vegeta board Babidi’s ship only to find themselves trapped! Can they save their friends and find their way out?'),
    (8, 3, 'Majin Buu Saga', 'Vegeta Attacks', 'At each stage of Babidi’s ship, Goku, Gohan, and Vegeta must face a fearsome warrior, each more powerful than the last. There’s no room for error! Even the tiniest mistake will enable Babidi to steal their energy for Majin Buu!'),
    (8, 4, 'Majin Buu Saga', 'Next Up, Goku', 'Babidi unleashes his monster Yakon to steal the Z-Fighters’ energy for Majin Buu. The battle at Stage Two is sure to be intense, as Yakon is one of the most fearsome creatures in the universe!'),
    (8, 5, 'Majin Buu Saga', 'Battle Supreme', 'At the World Martial Arts Tournament, the five remaining competitors enter the ring for an all-out Battle Royale! The fists fly as Number 18, Mighty Mask, and Mr. Satan duke it out to decide who will be the next Champion of the World!'),
    (8, 6, 'Majin Buu Saga', 'Eighteen Unmasks', 'The battle heats up as Number 18 and Mighty Mask take their fight to the skies! Number 18 gives it everything she’s got, but her attacks prove useless against her masked opponent. Could she find the edge she needs to win?'),
    (8, 7, 'Majin Buu Saga', 'Pay to Win', 'As the final bout of the tournament continues, Number 18 throws the defending champ for a loop by offering to throw the fight! Meanwhile, Babidi has selected his warrior for Stage 3: Dabura, King of the Demon World!'),
    (8, 8, 'Majin Buu Saga', 'Heart of a Villain', 'The intense battle between Gohan and Dabura rages on, but just as the Stage 3 clash reaches a heated peak, Dabura stops the fight! Why has the evil giant conceded, and what is the great discovery he claims to have made?'),
    (8, 9, 'Majin Buu Saga', 'The Dark Prince Returns', 'In an all-out assault against Vegeta, Babidi uses his power to undo the unsuspecting Prince from within! Vegeta is stripped of his good qualities by the wicked wizard, and becomes the heartless warrior that he once was!'),
    (8, 10, 'Majin Buu Saga', "Vegeta's Pride", 'Evil Vegeta gives Goku an ultimatum: fight – or watch him annihilate more innocent lives! Goku vows to settle the score between them once and for all, but the Supreme Kai steps between the Saiyans with a bold declaration!'),
    (8, 11, 'Majin Buu Saga', 'The Long Awaited Fight', 'The battle between Goku and Vegeta has begun! With Babidi’s magic enhancing his already incredible strength, Vegeta matches Goku move for move, but every blow the Saiyan Prince lands is a boost for Majin Buu!'),
    (8, 12, 'Majin Buu Saga', 'Magic Ball of Buu', 'With the fight between Goku and Vegeta supplying vast quantities of energy for Majin Buu, there’s not a moment to lose! Can Gohan muster up the strength to stop the evil wizard before it’s too late?'),
    (8, 13, 'Majin Buu Saga', 'Buu is Hatched!', 'The seal encasing Buu is finally broken! Supreme Kai insists on retreat, but Gohan refuses, launching an incredible series of energy attacks. When the shell opens, nothing is inside! Gohan, however, knows it’s no time to celebrate.'),
    (8, 14, 'Majin Buu Saga', 'The Losses Begin', 'With his big pink belly and infantile behavior, Buu doesn’t fit the bill of a galaxy destroyer – until he hurls Dabura into a cliff with a single blow! Gohan senses a limitless power, and the Supreme Kai insists this is the end!'),
    (8, 15, 'Majin Buu Saga', 'The Terror of Majin Buu', 'Supreme Kai must use his unique fighting powers to keep Buu at bay – or lose his life! One mile away, Goten and Trunks stumble upon Piccolo, still frozen in stone, and accidentally shatter him to pieces! And there’s more! The King of Demons returns!'),
    (8, 16, 'Majin Buu Saga', 'Meal Time', 'Free from the grip of Babidi, Vegeta decides to seek his revenge by destroying the monster Majin Buu. Assuming Gohan to be a victim of the voracious villain, the Super Saiyan goes ballistic. Can Vegeta bring down Buu?'),
    (8, 17, 'Majin Buu Saga', "The Warrior's Decision", 'With Goku and Gohan missing in action, it’s up to Vegeta to end Majin Buu’s reign of terror. The Saiyan prince gives it his all, but Buu’s powers may be more than he can handle!'),
    (8, 18, 'Majin Buu Saga', 'Final Atonement', 'Trunks and Goten save Vegeta from a savage beating, but the prideful prince is determined to destroy Majin Buu by himself. Vegeta is prepared to risk everything to defeat this foe, but is he really ready to give up his own life?'),
    (8, 19, 'Majin Buu Saga', 'Evil Lives On', 'Majin Buu’s flesh is scattered on the battlefield, but his mystical power is rebuilding the monster into one deadly piece! Babidi is recovering, too, having narrowly survived Piccolo’s attack!'),
    (8, 20, 'Majin Buu Saga', 'Find the Dragon Balls', 'Anxious to undo the massacre caused by Vegeta, Bulma and the others search frantically for the seven Dragon Balls! Meanwhile, the injured Goku finally awakens, and Dende uses his healing powers to bring him back to speed!'),
    (8, 21, 'Majin Buu Saga', 'Revival', 'Goku hatches a plan for defeating Majin Buu: Fusion! By joining two fighters of equal size and strength, an entirely new fighter can be created. But only one such pair remains – Goten and Trunks! Can the young half-Saiyans save the world?'),
    (8, 22, 'Majin Buu Saga', 'Global Announcement', 'Babidi seeks vengeance against Piccolo, Goten, and Trunks! Plastering images on everyone’s mind, Babidi threatens to terrorize humanity until the trio is brought forward! Meanwhile, Gohan is taken to Supreme Kai’s world!'),
    (8, 23, 'Majin Buu Saga', 'Learn to Fuse', 'Goku begins training Goten and Trunks in the art of Fusion. Meanwhile, Gohan, having been healed in Supreme Kai’s world, tries to remove the legendary Z-Sword to use in the fight against Majin Buu!'),
    (8, 24, 'Majin Buu Saga', 'The Z Sword', 'Majin Buu launches into a feeding frenzy, transforming an entire town’s population into chocolate! Gohan draws the ancient Z-Sword, Goku struggles to teach Goten and Trunks the art of Fusion, and an unlikely hero is asked to join the fight!'),
    (8, 25, 'Majin Buu Saga', 'Race to Capsule Corp.', 'As Goten and Trunks train to stop the vicious Majin Buu, Idasa’s jaded mother tells Babidi exactly where Trunks lives! The Z-Fighters must now find a way to stop the evil wizard before he reaches Capsule Corp!'),
    (8, 26, 'Majin Buu Saga', 'Super Saiyan 3?!', 'Trunks searches frantically for the lost dragon radar, and Goku powers-up to an unimaginable level: Super Saiyan 3! Will this newfound strength be enough to stop Majin Buu from destroying West City?'),
    (8, 27, 'Majin Buu Saga', "Buu's Mutiny", 'Goku uses his new Super Saiyan 3 abilities to combat the evil Majin Buu, buying Trunks the time he needs to locate the missing Dragon Radar. But now that Goku has started the fight, he may not be able to escape!'),
    (8, 28, 'Majin Buu Saga', 'The Fusion Dance', 'Liberated from his master, Majin Buu becomes even more destructive than before, wiping out entire cities in mere seconds! Earth’s only hope now rests on the shoulders of two young warriors: Goten and Trunks!'),
    (8, 29, 'Majin Buu Saga', "Goku's Time is Up", 'Tensions rise for Goten and Trunks as their duel with Majin Buu approaches. Meanwhile, Buu prepares for the upcoming battle by building himself a home! Elsewhere, Goku bids a poignant farewell as he finally returns to Other World.'),
    (8, 30, 'Majin Buu Saga', 'Return to Other World', 'While Trunks and Goten continue their quest to perfect the Fusion Technique, Gohan seeks to master the Z-Sword. Back on Earth, an encounter with a blind boy reveals that there is another side to the belligerent Buu!'),
    (8, 31, 'Majin Buu Saga', 'Out From the Broken Sword', 'When Gohan’s intense training breaks the legendary Z-Sword, all hope seems lost until Old Kai emerges and from the legendary weapon. Who is this aged fellow, and does he really have the incredible power he claims to possess?'),
    (8, 32, 'Majin Buu Saga', 'Gotenks is Born', 'After many comical misfires, Trunks and Goten finally perfect the Fusion technique, and Gotenks is born! Defying Piccolo’s command, the super-kid immediately leaves to go fight Majin Buu! Is Gotenks ready for the fight of his young life?'),
    (8, 33, 'Majin Buu Saga', 'Unlikely Friendship', 'As Majin Buu continues to terrorize humanity, a lone savior appears: Mr. Satan! His Megaton punch won’t be enough to stop the monster, but this unlikely hero may have a few surprises in store for Buu!'),
    (8, 34, 'Majin Buu Saga', 'I Kill No More', 'While the Z-Fighters continue training in preparation for their battle with Majin Buu, Mr. Satan devises some sneakier plans to take the villain down. But will he even need to carry them out? Is Majin Buu having a change of heart?'),
    (9, 1, 'Kid Buu Saga', 'The Evil of Men', 'When Mr. Satan inspires Majin Buu to give up his evil ways, it seems the professional pretender has really saved the world! But when a deranged madman suddenly spoils Buu’s good mood, the pink terror goes on another rampage!'),
    (9, 2, 'Kid Buu Saga', 'Buu Against Buu', 'The Battle of the Buus begins as Majin Buu fights his evil counterpart! The good Buu gets a taste of his own medicine when he’s turned into chocolate! Evil Buu gobbles him up, and a horrible transformation takes place! Who is this radical new Buu?'),
    (9, 3, 'Kid Buu Saga', 'Empty Planet', 'When the new and improved Majin Buu makes a surprise visit to the Lookout to challenge Gotenks, every second becomes a test of survival! And where are Trunks and Goten during the chaos that erupts?... Sound asleep, of course!'),
    (9, 4, 'Kid Buu Saga', 'Time Struggle', 'Before he can unleash his fury on the remaining Z-Fighters, Majin Buu is coaxed into the Hyperbolic Time Chamber. Inside, Trunks and Goten are training diligently, but will they have enough time to perfect their new moves before Majin Buu arrives?'),
    (9, 5, 'Kid Buu Saga', 'Super Moves of Gotenks', 'The long awaited rematch between Majin Buu and Gotenks begins! But when Gotenks’ fighting techniques come up short, he is forced to improvise – resulting in some of the craziest attack moves ever!'),
    (9, 6, 'Kid Buu Saga', 'Trapped in Forever', 'The battle between Gotenks and Majin Buu rages on inside the Hyperbolic Time Chamber. On the outside, family and friends wait anxiously for Gotenks and Piccolo to reappear. Can they successfully defeat Majin Buu and make it out alive?'),
    (9, 7, 'Kid Buu Saga', 'Feeding Frenzy', 'Powered by his insatiable hunger, Majin Buu escapes the Hyperbolic Time Chamber, leaving Piccolo and Gotenks trapped inside. Krillin and the gang are forced to fight the monster on their own. Will Buu finally make a meal out of the good guys?'),
    (9, 8, 'Kid Buu Saga', 'Gotenks is Awesome', 'Super Saiyan 3 Gotenks continues his fight with Majin Buu, and the Lookout is caught in the crossfire! As Gotenks turns up the power, so does Majin Buu – and by the time it’s over, one of them will be in way over his head!'),
    (9, 9, 'Kid Buu Saga', 'Unlucky Break', 'Gohan continues his training on the World of the Kais. Meanwhile, Gotenks briefly takes the upper hand in the battle with Majin Buu before his techniques begin to fall apart. Will Gohan be ready in time to step in and finish the fight?'),
    (9, 10, 'Kid Buu Saga', 'A Whole New Gohan', 'When Gotenks’ fusion unravels, it appears the end has finally come for Goten and Trunks. But just as things seem their worst, Gohan descends on the scene with his newly awakened powers! Finally, the tables are turning on Majin Buu!'),
    (9, 11, 'Kid Buu Saga', 'Search for Survivors', 'After being dominated on the battlefield, Majin Buu blows himself up in a desperate attempt to destroy Gohan! But is this just a ploy? Gohan seems to think so! Is Majin Buu plotting an ambush or simply trying to buy a little time?'),
    (9, 12, 'Kid Buu Saga', 'Majin Buu Transforms', 'Majin Buu reappears, ready for battle, but rather than continue his fight against Gohan, Buu stages a clever deception to absorb Gotenks and Piccolo. With the wisdom of Piccolo and the power of Super Saiyan Gotenks, Buu transforms into “Super Buu!”'),
    (9, 13, 'Kid Buu Saga', "The Old Kai's Weapon", 'After absorbing Piccolo and Gotenks, Majin Buu’s powers have increased exponentially! Armed with some new tricks, Majin Buu is poised for global destruction. Now that Gohan is alone and weakening, is there anyone who can stop the monster?'),
    (9, 14, 'Kid Buu Saga', 'Ready to Fuse?', 'Goku watches helplessly from Other World as Majin Buu sets his sights on Gohan. Luckily the Old Kai reveals a secret source of power that could save the day. Is Goku ready to bond with his son and put an end to Majin Buu’s reign of terror?'),
    (9, 15, 'Kid Buu Saga', 'Union of Rivals', 'After Majin Buu absorbs Gohan, Goku’s plan to join forces with his son is ruined. But an unlikely ally arrives on the scene – Vegeta! Will the Saiyan Prince put aside his differences and agree to merge with Goku?'),
    (9, 16, 'Kid Buu Saga', 'Meet Vegito', 'The bodies of Goku and Vegeta join to form a new Saiyan warrior. The monster Majin Buu is impressed by the strength of his new opponent, but refuses to take him seriously. Will Majin Buu’s arrogance be his undoing?'),
    (9, 17, 'Kid Buu Saga', 'Rip in the Universe', 'The newly-formed Saiyan warrior Super Vegito matches Majin Buu punch for punch. But the monster’s new opponent stirs up an uncontrollable anger within the very heart of the beast. Will Majin Buu’s frenzy mean the end of planet Earth?'),
    (9, 18, 'Kid Buu Saga', 'Vegito...Downsized', 'The battle rages on between Vegito and Majin Buu! The Super Saiyan Combo seems to have the fight well in hand. But is Vegito tempting fate by toying with Buu? What terrible tricks does the wily, pink monster still have up his sleeve?'),
    (9, 19, 'Kid Buu Saga', 'The Incredible Fighting Candy', 'Having been reduced to a coffee-flavored candy, it seems nothing can stop Vegito from being consumed by the evil Majin Buu. But when the gumdrop fights back, Buu realizes that the battle is far from over!'),
    (9, 20, 'Kid Buu Saga', 'The Innards of Buu', 'When Majin Buu absorbs Vegito, the fused Saiyan separates into Goku and Vegeta once again. Deep within the villain, they reveal their plan to rescue Gohan and the others. Can the duo survive the digestive process and carry out their mission?'),
    (9, 21, 'Kid Buu Saga', 'Mind Trap', 'Dangers abound as Goku and Vegeta continue their search for Gohan and inside of Majin Buu’s body! After meeting some disgusting bedfellows, they finally find what they’re looking for as they enter Majin Buu’s head!'),
    (9, 22, 'Kid Buu Saga', 'Deadly Vision', 'Goku and Vegeta reunite the others only to be attacked by Majin Buu! The showdown proves that fighting Buu inside his own head is a mind-bending experience. Can Goku and Vegeta survive in this twisted house of horrors where all is Buu?'),
    (9, 23, 'Kid Buu Saga', 'Evil Kid Buu!', 'When Super Buu’s body begins to mutate once again, Goku and Vegeta have to get out fast! But what awaits them should they manage to escape? What will the insidious Buu turn into next?'),
    (9, 24, 'Kid Buu Saga', 'End of Earth', "After the cords of attachment to the roly-poly Buu are cut by Vegeta, Majin Buu should mutate into a much weaker form. But instead he gets even stronger! This baffles everyone but Kibito Kai, who discloses Majin Buu's bizarre history!"),
    (9, 25, 'Kid Buu Saga', 'True Saiyans Fight Alone', "With Earth erased from existence, Majin Buu begins his search for Goku and Vegeta, leaving entire worlds destroyed in his wake. But when Buu's hunt leads him to the World of the Kais, Goku and Vegeta draw the line!"),
    (9, 26, 'Kid Buu Saga', 'Battle for the Universe Begins', 'With Majin Buu ready for a fight, Kibito Kai is stunned to see Goku and Vegeta playing a game of Rock, Paper, Scissors! Rather than use the Fusion Technique to join their powers, the duo has decided to fight Buu one at a time!'),
    (9, 27, 'Kid Buu Saga', "Vegeta's Respect", 'When Super Saiyan 3 Goku collapses from exhaustion, Vegeta enters the fight, but he doesn’t last long! Just as Majin Buu is about to deliver the deathblow, Goku makes a comeback!'),
    (9, 28, 'Kid Buu Saga', 'Minute of Desperation', "Goku's powers are fading, and he must end the battle before it's too late! Enter Vegeta, who begins a furious battle with Buu to buy Goku the time needed to gather energy. Outclassed by his opponent, can the Saiyan Prince survive!?"),
    (9, 29, 'Kid Buu Saga', 'Old Buu Emerges', 'When Vegeta falls, Mr. Satan steps in to take up the challenge! It appears the wannabe hero has signed his death warrant, but when Buu attempts to attack, the monster is crippled by agony!'),
    (9, 30, 'Kid Buu Saga', 'Earth Reborn', "As good Majin Buu wages an all-out war against his evil counterpart, Vegeta asks Dende to summon the Dragon on the new Planet Namek. With the good Buu's power dwindling, will Vegeta have enough time to carry out the final phase of his plan?"),
    (9, 31, 'Kid Buu Saga', 'Call to Action', 'Goku awaits the arrival of the Earthlings’ collective energy to vitalize the Spirit Bomb, but the energy isn’t coming! Have the people of the Earth turned a deaf ear to Vegeta’s plea for help at this most critical hour?'),
    (9, 32, 'Kid Buu Saga', 'People of Earth Unite', 'The foolish Earthlings ignore Goku, but when Mr. Satan asks for help, the humans have a change of heart. Will their outpouring of energy arrive in time? Goku can only wait and watch as Vegeta crumbles under the might of Majin Buu!'),
    (9, 33, 'Kid Buu Saga', 'Spirit Bomb Triumphant', 'After the good Buu and Mr. Satan free Vegeta, Goku launches the Spirit Bomb! Unfortunately, the weary Saiyan doesn’t have enough power to deliver the blast, and Buu sends it right back at him! Will Goku be destroyed by his own attack?'),
    (9, 34, 'Kid Buu Saga', 'Celebrations with Majin Buu', 'When Goku and his companions return to Earth after defeating Majin Buu, they are welcomed with open arms. But nobody is happy to see the good Buu! Can Mr. Satan’s pink pal manage to fit into society? Or is he destined to become an outcast?'),
    (9, 35, 'Kid Buu Saga', "He's Always Late", 'Goku has his hands full guarding four dragon eggs from the dangers of the wild, but even if he can save the baby dragons, he will soon face an even more dangerous peril: an angry Chi Chi!'),
    (9, 36, 'Kid Buu Saga', 'Granddaughter Pan', 'It’s been ten years since the demise of evil Majin Buu, and Earth is once again at peace. Gohan is a scholar. Trunks and Goten are strong, young teenagers! Vegeta and Bulma have a new daughter! And Goku is a grandfather!'),
    (9, 37, 'Kid Buu Saga', "Buu's Reincarnation", 'A new World Tournament is set to begin! With help from Majin Buu, Goku rigs the drawing so he faces a mysterious fighter in the first round of the finals! Is this timid, little village boy called Uub really as strong as Goku thinks?'),
    (9, 38, 'Kid Buu Saga', "Goku's Next Journey", 'Uub grows stronger as the battle rages, soon becoming the Saiyan’s equal, but before the match is decided, Goku makes a startling revelation! With his plan revealed, Goku and Uub depart the arena, leaving a stunned crowd in their wake.'),
]

# Dragon Ball specials (TMDB Specials): feed film keyword -> (canonical title, TMDB synopsis). Ordered: specific first.
DBZ_SPECIALS = [
    ('episode of bardock', 'Dragon Ball: Episode of Bardock (2011)', "The continuing adventures of Goku's father Bardock, who traveled through time and met new friends and enemies."),
    ('bardock', 'Dragon Ball Z: Bardock - The Father of Goku (1990)', 'The tale of Bardock, the father of Goku, and his rebellion against his master the mighty Frieza.'),
    ('summer vacation', 'Dragon Ball Z: Summer Vacation Special (1992)', 'In the streets of West City, Goku and Gohan, wearing sharp tuxedos, discuss the first three movies of Dragon Ball and the first seven of Dragon Ball Z.'),
    ('atsumare', 'Dragon Ball Z: Atsumare! Gokū Wārudo (1992)', 'Goku and his friends pose questions for the viewers about the Dragon Ball series.'),
    ('goku world', 'Dragon Ball Z: Atsumare! Gokū Wārudo (1992)', 'Goku and his friends pose questions for the viewers about the Dragon Ball series.'),
    ('history of trunks', 'Dragon Ball Z: The History of Trunks (1993)', "It has been thirteen years since the Androids began their killing rampage and Son Gohan is the only person fighting back. He takes Bulma's son Trunks as a student and even gives his own life to save Trunks's. Now Trunks must figure out a way to change this apocalyptic future."),
    ('eradicate the super saiyan', 'Dragon Ball: Plan to Eradicate the Super Saiyans (2010)', 'Dr. Raichi is one of the only survivors of the Tuffles, a race that once lived on Planet Plant before the coming of the Saiyans. The Saiyans not only massacred the entire Tuffle race, but also stole their technology and conquered the planet, renaming it Planet Vegeta in honor of their king. Raichi managed to escape with a capsule and found refuge on the Dark Planet, a world at the end of the universe. His only wish is to eradicate the last remaining Saiyans.'),
    ('eradicate the saiyan', 'Dragon Ball Z Side Story: Plan to Eradicate the Saiyans (1993)', "Dr. Raichi, a survivor of the Tuffle race that was eliminated from Planet Vegeta by the Saiyans, is trying to take revenge on the surviving Saiyans by killing them and Earth's population. Goku, Gohan, Piccolo, Trunks, and Vegeta must find and destroy generators emitting deadly Destron Gas before all life on Earth is extinguished, then find Raichi and stop him."),
    ('year-end', 'Looking Back at It All: The Dragon Ball Z Year-End Show! (1993)', 'Gohan and Goten are having a hot bath outside in the middle of winter. A dead Goku suddenly appears in front of his sons with the help of his Instant Transmission. The three Saiyans reflect back on the events that occurred during the Cell Games.'),
    ('looking back', 'Looking Back at It All: The Dragon Ball Z Year-End Show! (1993)', 'Gohan and Goten are having a hot bath outside in the middle of winter. A dead Goku suddenly appears in front of his sons with the help of his Instant Transmission. The three Saiyans reflect back on the events that occurred during the Cell Games.'),
    ('friends return', 'Dragon Ball: Yo! Son Goku and His Friends Return!! (2008)', "Goku and his family and friends encounter Vegeta's brother, and a threat from Vegeta's past shows up and causes trouble."),
    ('tree of might', 'Dragon Ball Z: The Tree of Might (1990)', None),
]

def _joint_nums(se):
    """House rule for joint slots: 1 ep -> (None, None); 2 eps -> "S05 E01+E02" (joint list);
    3+ consecutive eps in one season -> range "S05 E01-E03" (ep_end)."""
    if len(se) < 2:
        return None, None
    if len(se) == 2 or len({s for s, _ in se}) > 1:
        return None, [list(x) for x in se]
    return se[-1][1], None

# ── Gunsmith Cats (1995-96 OVA, 3 episodes; IMDb list, typos tidied) ─────────
DUCKTALES = {  # DuckTales (1987), IMDb list keyed on the feed's (season, episode): (name, synopsis)
    (1, 1): ("Treasure of the Golden Suns: Don't Give Up the Ship", "Part 1 of 5. Scrooge McDuck is forced to take in his three nephews Huey, Dewey, and Louie, when their Uncle Donald enlists in the Navy. As they learn to get along, the mysterious El Capitan hires the Beagle Boys to steal a small wooden ship from Scrooge's museum, saying it is a map to a real treasure ship."),
    (1, 2): ('Treasure of the Golden Suns: Wronguay in Ronguay', "Part 2 of 5. Having learned about the ship of gold, Scrooge and the triplets follow the map to South America, in a race with El Capitan, this time aided by Scrooge's archenemy, Flintheart Glomgold. Both parties are caught in the region's legendary Monsopies rainstorms."),
    (1, 3): ('Treasure of the Golden Suns: Three Ducks of the Condor', 'Part 3 of 5. An expert examines a coin from the sunken ship and declares it is from the legendary Valley of the Golden Suns. Scrooge flies to the Andes mountains to find the owner of a twin coin, and one half of the map leading to the Valley. He is aided by his nephew Donald, on temporary leave from the Navy, and pilot Launchpad McQuack.'),
    (1, 4): ('Treasure of the Golden Suns: Cold Duck', "After Scrooge goes off alone to follow the ocean currents to find the other half of the map, Launchpad and the boys follow his trail to Anarctica, where they are captured by a city of intelligent Penguins. they receive unexpected help from the boys' new governess, Mrs. Beakley, and her granddaughter Webbigail."),
    (1, 5): ('Treasure of the Golden Suns: Too Much of a Gold Thing', "Having completed the map, McDuck and Co. finally fly to the Valley of the Golden Suns. From outside they are stalked by El Capitan; from inside they are threatened by Scrooge's increasing greed, which leads him to recklessly risk all their lives against the Valley's booby traps."),
    (1, 6): ('Armstrong', "Gyro Gearloose builds a robot that can do anything efficiently and effectively. Then it goes berserk and takes over Scrooge's empire."),
    (1, 7): ("Luck o' the Ducks", 'Webigail befriends a leprechaun cast out by his people. Scrooge inadvertently saves the little man\'s life, and, knowing that his people have to grant him a wish, demands that he be given their legendary "Golden Caverns" in return. When the little people scheme to punish Scrooge for his greed, Webigail and her friend must save him.'),
    (1, 8): ('Where No Duck Has Gone Before', "Uncle Scrooge forecloses on a loan for a movie studio. To improve it, he instructs Gyro to make the set for a space show, as real as possible. When he does, Huey, Dewey, and Louie go to space with their hero 'Major Courage,' where they are captured by aliens. How will they defeat the aliens and return home? Does 'Major Courage' have 'what it takes' when it is not an act?"),
    (1, 9): ('Nothing to Fear', 'On a day when the McDuck family is trapped indoors by a thunderstorm, Magica DeSpell causes each of them to see living versions of their worst fears.'),
    (1, 10): ('Duck in the Iron Mask', 'Scrooge visits his old friend, Count Roy, of the mountain kingdom of Montedumas, only to find that his evil twin brother Ray has usurped the throne, and thrown Roy in jail wearing an iron mask.'),
    (1, 11): ('Much Ado About Scrooge', 'Scrooge and his nephews follow a trail to a remote island to find a lost play written by legendary playwright Drakespeare, followed by super-salesman Filler Brushbill.'),
    (1, 12): ('Spies in Their Eyes', 'Donald is hypnotized into stealing the control module for a prototype attack submarine Scrooge has developed for the Navy.'),
    (1, 13): ('Dime Enough for Luck', "Magica DeSpell enchants Scrooge's nephew Gladstone Gander into using his supernatural luck to infiltrate Scrooge's money bin and steal his Number One Dime, thus cursing himself with bad luck."),
    (1, 14): ('Jungle Duck', "A search for a lost silver statue causes Scrooge and the others to discover a jungle duck. Much to Mrs Beakley's surprise, the jungle duck is a Prince whom she was once a nanny to long ago."),
    (1, 15): ('Scroogerello', 'Scrooge is the servant boy for his evil stepbrothers and evil stepfather. His fairy godmother prepares him for the ball, where he falls in love with the princess. She is kidnapped! How will he rescue the princess before midnight?'),
    (1, 16): ('Top Duck', "Launchpad is terrified of making a fool of himself in front of his flying-ace family when all the McQuacks are to appear at an air show together. Launchpad is to fly Scrooge's experimental fighter plane, the Mc-X. But when the Beagle Boys sabotage his practice efforts and put themselves forward as its test pilots, the entire McQuack clan must bond together to stop an aerial assault on Scrooge's money bin."),
    (1, 17): ('Bermuda Triangle Tangle', "After a cargo ship is lost in the Bermuda Triangle, Scrooge and his nephews travel there to discover the Triangle's secret and find the missing crew."),
    (1, 18): ('The Status Seekers', 'Scrooge realizes that he is not acting like a rich snob, which makes him unpopular among other rich people. He tries to raise his social status by acting rich, but the price of this turns out to be too high for him.'),
    (1, 19): ('Sweet Duck of Youth', 'Thinking that he has become too old, Scrooge sets out to find the Fountain of Youth.'),
    (1, 20): ("Magica's Shadow War", "Magica De Spell's plan to magically use her shadow to retrieve Scrooge's number one dime backfires when her shadow overpowers her."),
    (1, 21): ("Launchpad's First Crash", 'After Launchpad crashes for a hundredth time, he and Scrooge remember how they first met (and crashed).'),
    (1, 22): ('Home Sweet Homer', 'In ancient Greece, evil sorceress Circe accidentally brings uncle Scrooge and the boys back in time, where they help a young king, Homer, to defeat her. Inspired by the ancient Greek epic poem The Odyssey.'),
    (1, 23): ('Duck to the Future', 'Magica DeSpell tricks uncle Scrooge and sends him 40 years into the future, in which she is in control. Scrooge must defeat her and return to his own time.'),
    (1, 24): ('Down and Out in Duckburg', 'Uncle Scrooge is challenged by someone collecting an old guarantee. Who will help Scrooge after the way he treated them? How will he reclaim his former wealth?'),
    (1, 25): ('Dr. Jekyll & Mr. McDuck', 'Uncle Scrooge uses a strange perfume he bought in an auction, which makes him go crazy. His nephews must find an antidote with the help of a famous British detective.'),
    (1, 26): ('Time Teasers', 'Gyro invents a time-stopping device, which gets stolen by the Beagle boys. The chase after the thieves brings Scrooge, his nephews, and Gyro centuries into the past, where they are all caught by pirates.'),
    (1, 27): ('Catch as Cash Can: Part 1 - A Drain on the Economy', "Flintheart Glomgold hires the Beagle boys to steal Scrooge's fortune, so that Glomgold could win the title of the richest duck in the world, and an amazing prize that comes with it."),
    (1, 28): ('Catch as Cash Can: Part 2 - A Whale of a Bad Time', 'Glomgold tries again to stop Scrooge from being declared the richest duck in the world, this time using a stolen submarine.'),
    (1, 29): ('Catch as Cash Can: Part 3 - Aqua Ducks', 'Scrooge must go to the bottom of the sea to recover his fortune, which was sunk in the previous episode.'),
    (1, 30): ('Catch as Cash Can: Part 4 - Working for Scales', 'After recovering his money from the bottom of the sea, Scrooge has very little time left to deliver it to Macaroon and be declared the richest duck in the world. Glomgold and the Beagle boys will stop at nothing to prevent this.'),
    (1, 31): ('Merit-Time Adventure', "A sea monster is attacking ships, and even abducts uncle Scrooge. It's up to the junior woodchucks to stop the monster, but only one of them knows how."),
    (1, 32): ('Ducky Horror Picture Show', 'Werewolf, Dracula, and other monsters come to Duckburg for an annual convention, wreaking havoc on the town and on Scrooge McDuck.'),
    (1, 33): ('The Golden Fleecing', 'Scrooge, his nephews and Launchpad must fight their way through harpies and a dragon to steal the legendary Golden Fleecing.'),
    (1, 34): ('Horse Scents', 'Flintheart Glomgold bets against Scrooge McDuck on horse racing, in a hope of becoming the richest duck in the world, and he is willing to use any means to ensure his victory.'),
    (1, 35): ("Duckworth's Revolt", 'After Duckworth is fired so he can find his own fortune, he and the nephews are captured and enslaved. How will they get back to Earth?'),
    (1, 36): ('Ducks of the West', "Scrooge's oil reserves are suddenly dried up. He goes to the land of the cowboys to find out why."),
    (1, 37): ('Pearl of Wisdom', 'A couple of thieves steal a huge pearl from Banana Island inhabitants and sell it to Scrooge. But the pearl turns out to be far more valuable than they thought.'),
    (1, 38): ('Once Upon a Dime', 'Uncle Scrooge tells the story of how he made his fortune.'),
    (1, 39): ('Dinosaur Ducks', "Scrooge and Launchpad go to the Lost World to get a dinosaur for Scrooge's zoo."),
    (1, 40): ('Sphinx for the Memories', 'Donald is mistaken for an Ancient Egyptian ruler, known as the Garbled One, whose spirit later takes over his body.'),
    (1, 41): ('Double-O-Duck', 'When a spy who looks exactly like Launchpad is caught, Launchpad is offered to impersonate that spy in order to foil an evil plot.'),
    (1, 42): ('Micro Ducks from Outer Space', 'Tiny aliens visit Earth and leave one of their machines behind. When Scrooge tries to use this machine, he creates a very small problem.'),
    (1, 43): ('Robot Robbers', 'Gyro creates giant robots for construction work, but Beagle Boys find another use for them.'),
    (1, 44): ('Send in the Clones', "Magica De Spell transforms the Beagle Boys into Scrooge's nephews and sends them to retrieve Scrooge's Number One Dime."),
    (1, 45): ('Lost Crown of Genghis Khan', 'Scrooge and his nephews must beat other treasure hunters and recover the lost crown of Genghis Khan from the Abominable Snowman.'),
    (1, 46): ('The Right Duck', "Thanks to Launchpad's stupidity, he and Dufus find themselves in a rocket heading for Mars. How will they get back?"),
    (1, 47): ('Back Out in the Outback', "Someone of something is attacking the sheep on the Scrooge's farm in Australia. He goes down there to investigate."),
    (1, 48): ('Sir Gyro de Gearloose', 'Fed up with just being considered a "Gadget Man," Gyro uses his time-tub to go back to medieval times to become a brave knight. However, his penchant for invention soon gets the better of him.'),
    (1, 49): ('Raiders of the Lost Harp', 'Scrooge discovers the Lost City of Troy, in which he finds a magic harp. But his claim on the harp is challenged by Magica DeSpell and the Minotaur.'),
    (1, 50): ('All Ducks on Deck', 'A strange creature who calls himself Phantom Blot steals a top secret jet in order to conquer the world. Scrooge, his nephews, and Launchpad team up with Donald to stop this evil plot.'),
    (1, 51): ('The Curse of Castle McDuck', 'Scrooge McDuck takes his nephews and Webby back to Scotland, visiting both Cottage McDuck, and Castle McDuck. However, the locals are fearful of the castle, claiming a supernatural hound haunts the grounds.'),
    (1, 52): ('Superdoo!', 'Dufus finds an alien crystal, which gives him superpowers.'),
    (1, 53): ('Earth Quack', 'Strange underground creatures settle under Duckburg and cause earthquakes for fun. Scrooge and his nephews go down to stop them.'),
    (1, 54): ("Magica's Magic Mirror / Take Me Out of the Ballgame", "Magica DeSpell tricks Scrooge with a magic mirror to get his lucky dime. / Duckworth becomes a baseball coach, even though he doesn't know a first thing about baseball."),
    (1, 55): ("Scrooge's Pet", 'Webbie has an idea to help Uncle Scrooge worry less about his money. However the pet causes more worry when it takes the new combination for the safe door.'),
    (1, 56): ('The Money Vanishes', "The Beagle Boys steal Gyro's teleportation device to get to the Scrooge's gold."),
    (1, 57): ('Back to the Klondike', 'Scrooge returns to the place where he started making his fortune, but finds more of his past than he expected.'),
    (1, 58): ('Master of the Djinni', 'McDuck and Glomgold race each other to find the magic lamp of Aladdin, but finding the lamp turns out to be just the beginning.'),
    (1, 59): ("Launchpad's Civil War", 'Launchpad is invited to participate in a reenactment of a civil war battle. He feels honored at first, but the honor turns out to be more of an insult.'),
    (1, 60): ('Hero for Hire', "After being fired by Scrooge, Launchpad is recruited as a movie hero, not realizing that he's being used by the Beagle Boys to rob Duckburg's banks."),
    (1, 61): ('Maid of the Myth', 'A group of vikings, who were cut off from civilization for centuries, attack Duckburg and abduct Mrs. Beakley. Scrooge and his team are off to the rescue.'),
    (1, 62): ('Hotel Strangeduck', 'Scrooge buys an old castle and tries to turn it into a hotel, but the castle appears to be haunted. Or is it?'),
    (1, 63): ('Duckman of Aquatraz', 'Scrooge is framed for the robbery of a famous painting and is sent to Aquatraz prison.'),
    (1, 64): ('The Uncrashable Hindentanic', 'Flintheart Glomgold gives Scrooge the challenge of turning a profit on the retired airship, the Hindentanic. However, when it looks like Scrooge may best him again, Glomgold prepares to sabotage the star-studded maiden voyage.'),
    (1, 65): ("'Till Nephews Do Us Part", "Scrooge's plans to merge McDuck Enterprises with Vanderbucks Industries soon includes a proposal of marriage when he falls for CEO Millionaira Vanderbucks."),
    (2, 1): ('Time Is Money: Part 1 - Marking Time', 'Glomgold sells a useless island to Scrooge, but upon learning that the island is rich in diamonds, he gets it back by trickery. Scrooge decides to travel back in time to prevent this from happening, but ends up in the distant past.'),
    (2, 2): ('Time Is Money: Part 2 - The Duck Who Would Be King', 'Scrooge tries to return to the present, after being stranded in prehistoric times. On the way he discovers stowaways – a cave duck named Bubba and his pet triceratops Tutsi.'),
    (2, 3): ('Time Is Money: Part 3 - Bubba Trubba', 'After returning to the present, Scrooge get his hands on the diamond mine, stolen from him by Glomgold in the previous episodes. Meanwhile, Bubba tries to get used to living in the modern world.'),
    (2, 4): ('Time Is Money: Part 4 - Ducks on the Lam', "Scrooge still has to pay 10 million to Glomgold for the diamond island. Glomgold will stop at nothing to sabotage Scrooge's attempts to pay him."),
    (2, 5): ("Time Is Money: Part 5 - Ali Bubba's Cave", 'Scrooge has one last chance to pay Glomgold and get the diamond island, but he is running out of time.'),
    (2, 6): ('Super DuckTales: Part 1 - Liquid Assets', "Scrooge hires accountant Fenton Crackshell to keep track of his fortune. When Fenton hears Scrooge wants his assets kept 'liquid,' he ends up dumping the entire fortune in Lake Dobegone, where the Beagle Boys soon find it."),
    (2, 7): ('Super DuckTales: Part 2 - Frozen Assets', 'After recovering his fortune, Scrooge asks Gyro Gearloose to build a security robot, which ends up keeping even Scrooge away from his fortune.'),
    (2, 8): ('Super DuckTales: Part 3 - Full Metal Duck', 'Gyro creates a wearable suit dubbed "Gizmoduck," which accidentally finds it\'s way into Fenton Crackshell\'s hands. However, Fenton soon uses the suit to become Duckburg\'s newest hero, much to the chagrin of the Beagle Boys.'),
    (2, 9): ('Super DuckTales: Part 4 - The Billionaire Beagle Boys Club', "The Beagle Boys manage to take control of Gizmoduck, and use him to make off with Scrooge's fortune."),
    (2, 10): ('Super DuckTales: Part 5 - Money to Burn', 'Scrooge tries to rescue his money bin from under the sea, but before he can get to it, the bin is taken away by alien robots.'),
    (3, 1): ('The Land of Trala La', 'Scrooge has a nervous breakdown from all the money problems, so he sets out to find a mythical Land of Trala La, where there is no money. But running away from money is not as simple as it sounds.'),
    (3, 2): ('Allowance Day', "Huey, Dewey and Louie's plan to make Scrooge think it's Saturday to get their allowances causes a global crisis."),
    (3, 3): ('Bubbeo & Juliet', 'Bubba falls in love with a girl next door. Unfortunately for both of them, their parents are engaged in a petty war with each other.'),
    (3, 4): ('The Good Muddahs', 'The Beagle Babes kidnap Webby for ransom, but then decide to keep her.'),
    (3, 5): ('My Mother the Psychic', "Fenton's mother is zapped by a TV set and gets the ability to predict the future, which quickly becomes a burden."),
    (3, 6): ('Metal Attraction', 'Gyro builds a robot maid and gives her emotions so she could do her job better. But things get out of control when the robot falls in love with Gizmoduck.'),
    (3, 7): ('Dough Ray Me', 'Gyro invents a device, which can duplicate any object. But the duplication process has an unexpected side effect, which puts Duckburg in serious jeopardy.'),
    (3, 8): ("Bubba's Big Brainstorm", "Tired of being dumb, Bubba uses Gyro's Thinking Hat to become smarter, only to discover that he has more value as a prehistoric goon."),
    (3, 9): ('The Big Flub', "Fenton uses one of Gyro's half-baked inventions, a levitating bubblegum, to make a fortune, but the success doesn't last."),
    (3, 10): ('A Case of Mistaken Secret Identity', "Fenton longs for the recognition of his heroic deeds as Gizmoduck. The situation really goes out of hand when people come to believe that Gizmoduck's secret identity is Launchpad."),
    (3, 11): ('Blue Collar Scrooge', 'Scrooge gets amnesia and ends up working at one of his own factories in terrible conditions. Eventually, this makes him realize the error of his ways, and become a more generous employer – well, at least a little bit.'),
    (3, 12): ('Beaglemania', "When trying to steal the prize money for a Rock and Roll contest, the Beagle Boys sing a song titled 'The Boogie Beagle Blues,' and end up impressing the crowd and winning the prize money! They soon become a music sensation."),
    (3, 13): ('Yuppy Ducks', 'After Scrooge is quarantined, his nephews take over the business with disastrous results.'),
    (3, 14): ('The Bride Wore Stripes', "Ma Beagle pretends to be Scrooge's wife to get half of his money."),
    (3, 15): ('The Unbreakable Bin', 'Gyro invents an unbreakable glass, which Scrooge uses to protect his money bin. But the glass has one weakness, and Magica DeSpell finds out about it.'),
    (3, 16): ('Attack of the Fifty-Foot Webby', 'Webby turns into a giant, after discovering a magic spring during an expedition to the jungle.'),
    (3, 17): ('The Masked Mallard', 'To improve his public image, Scrooge becomes a superhero. But that gets him in even more trouble.'),
    (3, 18): ('A DuckTales Valentine (Amour or Less)', "Scrooge steals Cupid's arrows from an ancient temple, which attracts the attention of the Greek gods. Things get even more complicated when Scrooge himself falls under the arrows' spell."),
    (4, 1): ('Ducky Mountain High', 'McDuck and Glomgold are trying to cheat each other out of getting a newly discovered gold deposit. But they may not be the best cheaters in the game anymore.'),
    (4, 2): ('Attack of the Metal Mites', "Glomgold's scientists create mites that eat metal. Glomgold tries to use them to ruin Scrooge."),
    (4, 3): ('The Duck Who Knew Too Much', 'While being on an unauthorized vacation, Fenton must stop spies who intend to rob Scrooge, but he has to avoid being seen by Scrooge at the same time.'),
    (4, 4): ('New Gizmo-Kids on the Block', "Fenton's mother accidentally shrinks the Gizmo-suit in a wash, which creates an opportunity for Huey, Dewey, or Louie to become the newest Duckburg's superhero. But which one of them will succeed?"),
    (4, 5): ("Scrooge's Last Adventure", "Scrooge and Fenton embark on a most dangerous quest inside a computer to save Scrooge's fortune from a computer glitch."),
    (4, 6): ('The Golden Goose: Part 1', "The mystical Golden Goose, which can turn anything to gold, accidentally falls into Scrooge's hands. Blinded by greed, Scrooge puts the entire world at risk."),
    (4, 7): ('The Golden Goose: Part 2', 'The Golden Goose goes out of control and threatens to turn the entire world into gold. Scrooge and his team have only one chance of stopping it.'),
}

CHARLIE_BROWN_SNOOPY = {  # The Charlie Brown and Snoopy Show (1983), IMDb, keyed on the feed's (season, episode)
    (1, 1): ("Snoopy's Cat Fight", "Charlie Brown can't pitch, Sally's struggles in school, Charlie Brown and Peppermint Patty share a desk, Lucy finds new ways to annoy Schroder. Lastly Snoopy, Linus, and Woodstock fight the cat next door for Linus' blanket."),
    (1, 2): ('Snoopy: Team Manager', "Lucy's garden, Re-Run's life, Linus loses his blanket, and Snoopy manages the baseball team."),
    (1, 3): ('Linus and Lucy', "Sally gets Snoopy's help with a school assignment, the gang plays football and plays in the snow, Lucy fawns over Schroder, Charlie has a kite flying fiasco, and the various ways Lucy tortures Linus."),
    (1, 4): ('Lucy vs. the World', "Lucy has to put up with a lot; but she can also dish it out with the best of them whether it's playing baseball, or putting up with her brother. Other stories include Peppermint Patty staying at Charlie Brown's house and Snoopy is nominated for an award."),
    (1, 5): ("Linus' Security Blanket", 'Episode shorts include "Snoopy & Woodstock," "Sally," "Piano," "Baseball," "Sunset," "Football," "Security Blanket," "Kite," "Woodstock," and "Clinging Snoopy."'),
    (1, 6): ("Snoopy: Man's Best Friend", 'Snoopy is a complex dog. Various stories include his amorous side, his playful side, his role as a protector, a watchdog, and even a rescue dog.'),
    (1, 7): ('Snoopy the Psychiatrist', "Lucy picks on Charlie Brown driving him to seek help from Snoopy. Charlie Brown and Linus try to fly a kite. Peppermint Patty and Snoopy go to a dance. Thiebault borrows Charlie Brown's baseball mitt and then insults Peppermint Patty and Marcie."),
    (1, 8): ("You Can't Win, Charlie Brown", 'Short stories include Charlie Brown and Snoopy discussing puppy training, Rerun contributing to the baseball team, Lucy and Linus playing in the snow, and Peppermint Patty and Marcie in school among many others.'),
    (1, 9): ('The Lost Ballpark', "Charlie Brown walks funny, Marcie finds her mean streak after a boy develops a crush on her, Linus and Snoopy go truffle hunting, and Charlie Brown's team suffers setback after setback."),
    (1, 10): ("Snoopy's Football Career", "Peppermint Patty is accused of stealing her teacher's gold stars and she enlists Snoopy's help in order to clear her name. Linus claims someone stole his blanket; the search leads to a likely culprit. Schroder's piano playing elicits many varied reactions. The gang tries to teach each other how to play football leading to hilarious moments."),
    (1, 11): ('Chaos in the Classroom', "Sally's interesting theories about schooling and her trouble with a kid whose ruler she borrowed. The kids play football leading to Lucy pulling the football away from Charlie Brown. Marcie and Peppermint Patty become school crossing guards. Linus' blanket has a mind of its own and begins to annoy Lucy. Charlie Brown's team goes through the predictable struggles."),
    (1, 12): ("It's That Team Spirit, Charlie Brown", "Snoopy uses various techniques to get a hold of Linus' blanket including acting like a vulture. Peppermint Patty continues to struggle in school to the point where she threatens to drop out and hang out with Snoopy all day. Re-Run goes for a ride on his mother's bicycle. Charlie Brown tries to coach up his baseball team."),
    (1, 13): ('Lucy Loves Schroeder', "Charlie Brown tangles with the Kite-Eating Tree. Snoopy eats Sally's homework. The gang goes to summer camp where Peppermint Patty confronts the little red-haired girl. Lucy fawns over Schroder unsuccessfully. Something that goes bump in the night scares Snoopy, so he seeks help from Lucy."),
    (2, 1): ('Snoopy and the Giant', "Snoopy breaks his foot and must wear a cast, which proves complicated when he has to play for Peppermint Patty's baseball team. Meanwhile, Woodstock grows a beanstalk to the sky, where he and Snoopy meet a cookie-hoarding giant. Finally, the youngest of the Van Pelts has to deal with various problems."),
    (2, 2): ("Snoopy's Brother Spike", "Peppermint Patty asks Charlie Brown for help with her team. Linus waits up for the Great Pumpkin while Charlie Brown and Peppermint Patty go bowling. Snoopy's older brother Spike vists."),
    (2, 3): ("Snoopy's Robot", "Snoopy drives the gang to a computer camp. Once they explore the world of computers and Snoopy plays with a robot. Linus starts a clinic for kids that have security blankets. Snoopy goes to visit Spike in the desert taking Linus' blanket with him. Charlie Brown and Peppermint Patty go on a date. Later Marcie and Peppermint Patty both develop a crush on Charlie Brown."),
    (2, 4): ("Peppermint Patty's School Days", "Peppermint Patty's struggles in school are chronicled. Snoopy develops a cool trick after his antics begin to wear on the kids' nerves. Schroeder doesn't know how to get to piano camp. The gang flys him there on Snoopy's doghouse."),
    (2, 5): ("Sally's Sweet Babboo", "Charlie Brown reflects on his most memorable Christmas while Sally and Lucy prepare for Valentine's Day and Peppermint Patty writes an award-winning essay on Snoopy."),
}
BEYBLADE = {  # Beyblade (2001) TMDB: S1 = Beyblade, S2 = V-Force, S3 = G-Revolution; feed '1x48' / '2x01'
    (1, 1): ('The Blade Raider', 'Tyson is caught up in the sport of Beyblading, but can he balance Beyblading and martial arts?'),
    (1, 2): ('Day of the Dragoon', 'When Tyson and Kai end up battling against each other, Tyson is easily defeated. Can he unlock a mythical bit beast to even the score?'),
    (1, 3): ('Take It to the Max', "Can Kenny's friendship with Tyson continue when a new kid named Max seems to be stealing Tyson away?"),
    (1, 4): ('The Qualifier Begins', 'Max and Tyson arrive at the tournament and Tyson faces his first opponent.'),
    (1, 5): ('Draciel of Approval', 'The first matchup in the semi-finals is Max vs. Kai. Can Max pull the upset off without a bitbeast giving him support?'),
    (1, 6): ('Dragoon Storm', 'The mysterious blader Ray and Tyson do battle in the second round. Can Tyson survive the mysterious Tiger Claw Attack?'),
    (1, 7): ('Thirteen Candles', "The National Beyblade Championship Match is set – with Tyson facing off against reigning champion, Kai. It's not until Grandpa throws a surprise party for Tyson that the rookie sensation realizes he has forgotten his own birthday, but what will Kai have in store for him?"),
    (1, 8): ("Bladin' In The Streets", "Tyson and his new team, the Bladebreakers, prepare for the World Championships. Kai seems to reject his newfound team and leads them on a chase through the streets. That's where the guys learn some lessons about Beyblading from some very mysterious 'bladers."),
    (1, 9): ('Showdown in Hong Kong', "Our heroes arrive in Hong Kong on a stop-over to the Asian World   Championships when they run into Ray's old gang, the White Tigers. Naturally, a Beyblade battle quickly ensues."),
    (1, 10): ('Battle in the Sky', "The Bladebreakers discover that them and the White Tigers are in different divisons. To face them, they'll have to make it to the finals, but can the Unknown Tall Boys shock everyone and defeat the Bladebreakers ending all national title hopes?"),
    (1, 11): ('Bye Bye Bit Beast', 'Kevin decides to try and destroy Ray by stealing his data. What will happen if Kevin succeeds? Will the Bladebreakers have any chance of winning the Asian tournament, or will something worse happen?'),
    (1, 12): ('Adios Bladebreakers', 'With his bitbeast gone, Ray loses all confidence and decides to leave the Bladebreakers. Can Tyson convience him to come back, or will Mariah convience him that the White Tigers team is his real home?'),
    (1, 13): ('Crouching Lion, Hidden Tiger', 'With the Bladebreakers having impressed everyone, the White Tigers decide to get serious. Can they show everyone why they are the best?'),
    (1, 14): ('The Race is On!', 'A rockslide makes Tyson and Ray fall behind on their way to the semi-final matchup. Can they make it on time, or will a forfit keep the Bladebreakers from a showdown with the White Tigers?'),
    (1, 15): ('Going for the Gold', "The Asian finals begin between Max and Gary, but Gary's open-mindedness makes everyone think he can't win a thing. Will Gary's true wrath be unleashed to show why he battles instead of Kevin?"),
    (1, 16): ('My Enemy, My Friend', 'Ray and Mariah get ready to go head to head, but can these two lovers put aside their feelings for the match. Maybe their bitbeasts will have something to say about it.'),
    (1, 17): ('A Score to Settle', "When Tyson and Lee's matchup turns out to be a draw, it's up to Ray to defeat his old team and keep Driger. How will Driger and Ray react to this news?"),
    (1, 18): ('A Star is Born', 'With the Asian Tournament over, the Bladebreakers head home for a small break, but what will happen now that Tyson feels he has power?'),
    (1, 19): ('Under the Microscope', 'Max insists on seeing his mom before the American tournament, but what will he do when he finds out she works for the opposing team?'),
    (1, 20): ('All Relative', "After their non-competition loss to Emily of the All Starz at the BBA Research Center, the Blade Breakers sneak around the high-tech facility, hoping to learn more about their competition. There, they confront two other All Starz, and Max learns more about his Mom's job at the BBA – specifically, a rumor of why Max wasn't asked to join the All Starz Team."),
    (1, 21): ('Practice Makes Perfect', 'Can the Bladebreakers gain their confidence back after seeing all the fancy American equipment?'),
    (1, 22): ('Blading with the Stars!', 'When Max participates in a charity Beyblade event, he must teach Emily what team work is all about. Can he succeed?'),
    (1, 23): ('Showdown in Vegas', 'The American tournament begins in Las Vegas. Will Kai decide to show the All Starz his true power?'),
    (1, 24): ('Viva Las Vegas', 'The Blade Breakers decide to study the All Starz moves so they can become stronger. Will they succeed?'),
    (1, 25): ('My Way or the Highway', 'When Tyson gets a stomachache before the semi-finals, Kai must step up and take his place. Can the Bladebreakers keep their momentum going in the mysterious New Jersey Turnpike?'),
    (1, 26): ('Catch a Shooting All-Star', "Tyson's health is restored before the finals, so he gets ready to battle again. Can Max help them realize he can defeat his mom's team, or will Kai get the final spot?"),
    (1, 27): ('The Battle of America', 'The finals continue. Can the Blade Breakers muster the strength to win, or will the All Starz become the new American Champions?'),
    (1, 28): ('Bottom of the Ninth', "It's Max versus Michael for the American team championship. Which team will end up being victorious?"),
    (1, 29): ('Play It Again, Dizzi!', 'Kenny ponders how the Bladebreakers got together, and he wonders what the next touranment will bring.'),
    (1, 30): ('Cruising for a Bruising', 'When the Bladebreakers run into Robert on a ship to Russia, they realize just how much their bitbeasts need to develop. Can they learn how to gain the strength needed?'),
    (1, 31): ('London Calling', "When the Bladebreakers arrive in London, a mysterious tape about evil bitbeasts is waiting for Tyson. Can they interpret what Tyson's father is trying to tell them before they encounter an evil bitbeast, or is it already to late?"),
    (1, 32): ('Darkness at the End of the Tunnel', 'The Dark Bladers try once again to steal the Bladebreakers bitbeasts and turn them evil in a subway tunnel. Will they succeed?'),
    (1, 33): ('Last Tangle in Paris', 'The Blade Breakers arrive in Paris, but the Dark Bladers follow them there. Can the Blade Breakers handle one more battle with the Dark Bladers, or will additional and unexpected help come to save them?'),
    (1, 34): ('Art Attack', 'Tyson determines to battle the blader named Oliver, but does he have any chance at victory?'),
    (1, 35): ('When in Rome... Beyblade', "The Blade Breakers arrive in Rome to battle against their next opponent, Enrique. Can Tyson finally successfully defeat one of Europe's top bladers, or will he learn that he has a lot of skills to develop?"),
    (1, 36): ('Deja Vu All Over Again', "Tyson determines that he must defeat Enrique if his reputation as a top Beyblader is to be restored, but when Oliver arrives it becomes 2 of Europe's top bladers against Tyson's ego. Can he figure out a way to show that bitbeasts should be used for more than just power?"),
    (1, 37): ('A Knight to Remember', "Enrique and Oliver take the Blade Breakers to Robert's mansion, but can Tyson get his rematch against Robert, or will this Johnny character interfer?"),
    (1, 38): ('Olympia Challenge', 'The Blade Breakers decide to challenge Robert, Johnny, Enrique, and Oliver to a team battle. They accept, but can ""The Majestics"" work together as a team when they\'ve been individual fighters their entire life?'),
    (1, 39): ('A Majestic Battle... A Majestic Victory?', "It's Kai versus Johnny and Tyson versus Robert for the right to go to the World Championships in Russia. Who will win the bout?"),
    (1, 40): ('Hot Battle in a Cold Town', 'A mysterious man named Boris invites the Bladebreakers to his physilities for a practice battle. Should they trust him, and if they do, then can they win the battle?'),
    (1, 41): ('Out of the Past', "Kai investigates Boris' Abbey since he feels some sort of draw to it. What will he find? Also, Max meets up with the All Starz and Ray meets up with the White Tigers. Why have they come to Russia?"),
    (1, 42): ('Drawn to the Darkness', 'Kai must choose whether he wants the power of Dark Dranzer or the friendship of the Blade Breakers. Which will he decide?'),
    (1, 43): ('Live and Let Kai!', "While the Bladebreakers try and find out what Kai's doing, the All Starz get ready to scrimmage the Demolition Boys, but when Kai shows up on the Demolition Boys and challenges all 4 All Starz at once, you know fire works will erupt. What will he do?"),
    (1, 44): ('Losing Kai', 'The White Tigers determine to get revenge on Kai for the All Starz, but will they need to when Tyson and the Bladebreakers decide to try and talk some sense into Kai?'),
    (1, 45): ('Breaking the Ice', "Kai decides he wants all of the bitbeast, so he challenges the Bladebreakers to a match. Will they stand a chance without Max, who's with his mom at the airport?"),
    (1, 46): ('First Strike', "Kai and Tyson's father appear to let everyone know what Biovalt is really up to. Can the Bladebreakers find a way to stop them?"),
    (1, 47): ('A Lesson for Tyson', 'The Majestics show up in Russia with a challenge for the Bladebreakers, defeat them in a match, or lose their bitbeasts. Why have they come to Russia, and why do they want the Bladebreakes bitbeasts?'),
    (1, 48): ('Victory in Defeat', 'Kai is given a tempting offer from his grandfather Voltaire, use dark Dranzer, or risk losing Dranzer forever. Will he give in?'),
    (1, 49): ('A Wicked Wind Blows', 'With Kai losing in the first round, Ray must find some way to even up the score. Can he find the strength to do so, and if he does, will he risk losing Drigger forever?'),
    (1, 50): ('New and Cyber-Improved...', "When Tala gets cyber implants and Tyson gets new blading equipment, you know their match strategy's are bound to change, but just how will the changes affect the championship?"),
    (1, 51): ('Final Showdown', 'A grave meeting is held between the Majestics, Kevin of the White Tigers, and the Dark Bladers in case Tyson should lose the match. Can Tyson survive in this other dimension, or will the Demolition Boys become World Champions and rulers?'),
    (2, 1): ('Shot Down in Flames!', 'Tyson starts the new season arrogant as always. There is a new blader in town called Mr. X. Can Tyson defeat him?'),
    (2, 2): ('The Search for Mr. X', 'Tyson is more determined than ever to face Mr. X again. Meanwhile Ray and Max are defeated by mysterious bladers as well. Is Chief to late to stop Tyson from battling Mr. X again?'),
    (2, 3): ('Unseen and Unleashed', "Chief in on his way to tell Tyson what he has learned about the three mysterious bladers. We find out Mr. X's name is Ozuma. Chief, Tyson, and Hilary are to mee to discuss tactics. When Tyson arrives to meet the other two they are gone. What happened to them?"),
    (2, 4): ('Searching for Dragoon', 'Tyson has to track down what happened to Chief and Hilary. He is led to a run down boat that transports him to a room with a glass front. Can Tyson save his two friends?'),
    (2, 5): ("Guess Who's Back in Town?", 'Chief can only assume that since Tyson, Ray, and Max have been defeated by mysterious bladers that Kai is next. Is Chief right? Meanwhile Kai is back in school and meets a guy named Wyatt.'),
    (2, 6): ('The Magtram Threat', 'Gideon, the one who is bhind the kidnapping of Chief and Hilary, has got him a new recruit by the name of Snakey. Can Snakey defeat Tyson and Dragoon?'),
    (2, 7): ('The Reunion Begins', "After reviewing Tyson and Snakey's battle Dizzi and Chief figure out Snakey was using a Magtram-enhanced Beyblade. The same metal that was used on the boat Tyson was on. Gideon has a team called Team Psykick. Can the Bladebreakers defeat Team Psykick?"),
    (2, 8): ('Return of the Bladebreakers!', 'The newly reunited Bladebreakers begin training for their upcoming battle with Team Psykick.  Armed with the new MG Core, which will give the team complete control of their blades, one question comes to mind. Can they manage to learn to use the core correctly?'),
    (2, 9): ('La Isla Bey-Nita', 'The Bladebreakers are trapped on an island. Max is the first to battle against a character named Chameleon, but what tricks does Chameleon have in store for him, and why did team Psykick drag them all the way out to an unknown island?'),
    (2, 10): ('The Island of No Return', 'Ray is next to battle a guy named Bat, who can see in the dark. Can Ray overcome not seeing in the dark to keep his bitbeast Driger?'),
    (2, 11): ('The Evil Island of Dr. B', "After Kai's win against Figel, he joins Kenny and Hilary to resume their journey to the lighthouse. From there the heroes hope to get a clear satellite signal to call for help.  Will they be able to call for help before Daryl takes on the wounded Tyson?"),
    (2, 12): ('Bring Me Dranzer', "Gideon plans to create his own Cyber Bit Beasts but lacks vital data on Dranzer. Meanwhile the Saint Shields plan their own attack on Dranzer and send Dunga to do the job. Will the Blade Breakers realize there's a conspiracy against them before it's too late?"),
    (2, 13): ('Testing One, Two, Three', "Joseph decides to find out what the Psykicks are doing with the data they've collected from their matchups with the BladeBreakers. His discoveries cause them to escalate matchups against the BladeBreakers as they secretly test Max & Ray in a two vs. two battle against Miriam & Joseph. Who will win the match-up, and just what did Joseph discover?"),
    (2, 14): ('Gideon Raises Gerry!', 'Doctor B unveils the first Cyber Bit Beast to the world. Gerry from Team Psykick is chosen to be the first to wield this new Beyblade. What can possibly go wrong with an untested, experimental, extremely powerful, Mad Scientist created Bit Beast?'),
    (2, 15): ('Show Me the Bit-Beasts!', "Kenny discovers that someone has made copies of all the Blade Breakers' Bit Beasts and the team decides to prepare themselves for battle. Hilary feels left out because she can't see the team's Bit Beasts so she joins the gang in their training."),
    (2, 16): ("Team Psykick's New Recruit", "Dr. B and his team have finally perfected the Cyber Bit Beast and are ready to test it on the BladeBreakers, but first they need to find a Blader strong enough to take on the challenge.  Will Kai's classmate Wyatt be just the Blader they're looking for?"),
    (2, 17): ("Hilary's Bey-B-Cue", "Getting fed up with the rest of the team, Tyson decides to quit. This doesn't last for long, when his insatiable appetite lures him back into the fold.  Grandpa's fishing doesn't work out according to plan either. The catch of the day has turned the tides on this old man, but who are these new bladers that save him. Can the BladeBreakers trust them?"),
    (2, 18): ('When Friends Become Foes', "The Blade Breakers sneak into Doctor B's lab, where Tyson learns that the dreaded Psykick's have recruited his new pal Kane into their ranks, but can they convience them to leave the Psykicks, or have the Cyber Bit Beast already begun taking them over?"),
    (2, 19): ('Their Own Private Battles', 'After seeing the Cyber Bit Beasts in action, Tyson vows to do whatever it takes to beat them. Ray develops an unexpected friendship with Salima of Team Psykick in the hopes of learning more about their next challenge, but is she really to be trusted, or is she planning on taking Ray down some how?'),
    (2, 20): ('The Power Half Hour!!', 'Tyson struggles to control his new ""tricked out"" Beyblade. His frustration leads him to battle Ozuma who is always around to teach Tyson a lesson when he needs one. Will Tyson finally be able to defeat Ozuma, or will Ozuma destroy Tyson\'s blade and ego for good?'),
    (2, 21): ('The Battle Tower Showdown', 'The Bladebreakers and Hilary head for their battle against Team Psykick in a helicopter. They are met in the Battle Tower by robots. Luckily the Saint Shields are there to cover their backs. Max and Jim are the first two to battle. Who will win the first round?'),
    (2, 22): ('Max Takes One for the Team', 'Jim and Cyber Draciel appear to have the upper hand due to the Cyber repair system, but can Max find a way to make defeat into victory?'),
    (2, 23): ('The Bigger the Cyber-Driger...The Harder It Falls...', "Selima and Ray battle head to head in the second match up, but will Cyber Driger prove to be too strong for Driger, or will driger's previous power fully return?"),
    (2, 24): ('Ghost in the Machine', "Kai squares off against Goki on Level Four of Gideon's Battle Tower. But when his real opponent turns out to be the ghost of his friend Wyatt, Kai finds himself helpless.  Can the Bladebreakers help Kai lay his guilt to rest or is this the Bladebreakers final defeat?"),
    (2, 25): ('Raising Kane!!', 'The final battle between Tyson and Kane begins with a shock. Kane actually decides to battle fair without the help of Cyber Dragoon, but can this resolve last long, or will Tyson and Dragoon see powers they never could have imagined?'),
    (2, 26): ('Cyber Dragoon Takes Control!', 'Tyson faces off against Kane only to discover that Kane has fallen under the control of his Cyber Bit Beast. Tyson reluctantly tells Dragoon to give up, but will Dragoon listen, or will his loyal Bit Beast summon the strength to keep fighting and inspire Tyson to do the same?'),
    (2, 27): ('Building the Perfect Bit Beast!', 'At the conclusion of the fierce battle between Tyson and Kane, the Battle Tower starts to collapse around them.  During their mad dash to make it out of the building, Max realizes that Draciel is still inside. How will he get him out of there?'),
    (2, 28): ('Hot Rock', "The Bladebreakers and Hilary head off for NYC. Max's mom Judy is their to greet them. Judy unveils a secret rock to the BladeBreakers, but when it gets stolen its up to the BladeBreakers to get it back. Can they succeed?"),
    (2, 29): ("A Friend's Cry / Bad Seed in the Big Apple", "As it turns out Max's friend Alan was part of the scheme to steal the powerful rock. Can Max manage to defeat Alan and get him to reveal what's going on?"),
    (2, 30): ('Get a Piece of the Rock!', 'The Bladebreakers return to Japan accompanied by Judy. Mr. Dickenson tells all of them about a partner he used to work with named Dr. Zagart. Tyson has to learn to control his new Beyblade Dragoon V2. The Saint Shields decide to efeat Tyson before he can learn to control his new blade, but will they succeed when a mysterious fighter appears?'),
    (2, 31): ('Attack of the Rock Bit Beast', 'The search for the missing rock  and the mysterious Dr. Zagart goes on. Unfortunately the BladeBreakers are at a loss as to where they should look. When Foxy challenges Ray to a match, the team unknowingly moves a step closer to solving the mystery, but first they have to defeat Foxy. Will they succeed?'),
    (2, 32): ('Lots of Questions... Few Answers', "After Foxy's attack, the team has many questions, but few answers. Who was behind the attack and how is the rock involved?"),
    (2, 33): ('Rock Bottom!', "When Ray loses Driger to Dunga's Vortex Ape, the Bladebreakers resolve to go back into training and rescue him. But will they be able to save Driger without putting themselves into further jeopardy? And what is Dunga's real reason for taking Ray's bit-beast?"),
    (2, 34): ('Itzy Bey-Itzy Spider', 'Tyson runs into a sticky situation while trying to figure out how to get Driger back.  Net and his Bit Beast Spider coax Tyson into releasing Dragoon so they can capture it for their own goals. Will he be able to escape from this web slinging assassin?'),
    (2, 35): ('See No Bit Beast, Hear No Bit Beast', "There's a new Blader after Kai's Bit beast and he's ready for battle. The only problem is he's quiet as the wind and as strong as a hurricane. How can Kai possibly beat an opponent that he can't even see?"),
    (2, 36): ('Friends and Enemies', 'After Max is ambushed, Mariam discovers that Dr. K is using Power Injection to make the Bit Beast, Tyranno stronger. When Mariam destroys much of the building, she and Max must work together to find a way out. But will Mariam capture Draciel once they escape?'),
    (2, 37): ('Beybattle at the Bit Beast Corral', 'With the goal of acquiring the BladeBreakers Bit Beasts and sealing them in a rock, The Saint Shields challenge them to a match at an abandoned amusement park. The first match is Miriam versus Max, but will Max manage to win, or is Draciel done for?'),
    (2, 38): ('The Fate Of The Spark Battle', "The Saint Shields have already captured Ray's Bit Beast, Driger, and now they've set their sights on capturing Kai's Dranzer. Dunga goes into battle against Kai and the fight intensifies as the blades race along the rails of an abandoned roller coaster to what looks like their doom. Can any of them survive?"),
    (2, 39): ('The Bit Beast Bond', 'Ozuma, leader of the Saint Shields gang makes a final play for the BladeBreakers four Bit Beasts. During his battle with Tyson, it is revealed that he comes from an ancient group that is sworn to capture and contain all the Bit Beasts in the world, but will this new found knowledge give the BladeBreakers the know how to defeat Ozuma, or is Dragoon done or?'),
    (2, 40): ('Squeeze Play', 'Pleased that the Saint Shields no longer wish to seal the four Bit Beasts, Dr. K gives a new Blader, Denny, a powerful rock Bit Beast named Clarken and orders him to capture the four Sacred Bit Beasts.  Meanwhile, Zeo catches up with the Bladebreakers and shows them his invitation to the upcoming World Championships, but when Denny shows up to destroy their practice, can Zeo help them win the day?'),
    (2, 41): ("Who's Your Daddy?", "The BladeBreakers show up at the World Championship Tournament and go up into the stands to cheer on Zeo who's fighting in the preliminaries, but a shocking turn of events is about to occur for Zeo. Find out what it is when you finally meet Zeo's dad."),
    (2, 42): ('Fortunes Dear and Dire', 'Zeo focuses on Beyblade training with his father Zagart. The most powerful rock Bit-Beast named Cerberus is designated for Zeo, but he must first be able to summon it. Zeo trains furiously, but the elusive Bit Beast never fully materializes. Meanwhile, the Bladebreakers must choose their two team-pairs for the World Beyblade Championships, but what will be their teams and can Zeo really become the BladeBreakers enemy?'),
    (2, 43): ("Kai's Royal Flush", "While all that the BladeBreakers can think of are the finals, Kai can't stop obsessing about King and Queen.  With a brand new Beyblade crafted for him by Kenny, Kai longs for a rematch. But Kai isn't the only one with the royal pair on his mind. Doctor K tracks the duo down and offers them a chance to team up with her so they can capture and wield the power of the four sacred Bit Beasts together. What will King and Queen end up doing, and can Kai get his revenge on the duo?"),
    (2, 44): ('The Calm Before the Storm', "After disappearing thirty years ago, Zagart confronts Mr. Dickenson, forcing him to enter Zeo in the World Championship Finals. He reveals that Zeo is his son and that he won't show mercy when he confronts the Bladebreakers in the tournament. Meanwhile, the pairings for the finals are announced, but King and Queen want to start the fun a bit early. Can Mr. Dickenson stop chaos from occuring, or will it take someone else a bit stronger?"),
    (2, 45): ('Zeo vs. Ozuma', 'The Beyblade World Championship Finals are underway and eight teams convene to compete for the title. The BladeBreakers are shocked to see that their old friend Zeo is in the competition and Tyson confronts him to find out why he has decided to compete against them. Will Zeo reveal the truth, or can the Saint Shields knock Zeo out of the tournament?'),
    (2, 46): ('Black & White Evil Powers', 'The World Beyblade Championships continue and the next round has Tyson and Max squaring off against Kane and Jim. Kane and Jim decide to have a little practice battle at the beach. But King and Queen show up for a surprise attack. Can Kane and Jim hold off the duo, or will the BladeBreakers or Saint Shields manage to show up and save the day?'),
    (2, 47): ('Deceit From Above', "In the Semi-Final round of the World Beyblade Championships, Max & Tyson take on King & Queen. Doctor K tempts Queen into using a vicious new attack ring she's created called 'The Shredder'. Can Max and Tyson manage to overcome this new piece, or will they lose their sacred Bit Beasts?"),
    (2, 48): ('Phoenix Falling', "The second semi-final begins with Ray battling Gordo and Kai battling Zeo. Can the BladeBreakers manage to end Zeo's dreams now, or will the BladeBreakers have their worst nightmare yet come forth?"),
    (2, 49): ('The Enemy Within', "The Bladebreakers begin to lose faith in each other, and Tyson contemplates Zeo's betrayal of them. Tyson decides to confront Zeo about it, but what will be the result, and will the other Bladebreakers support him?"),
    (2, 50): ('Clash Of The Tyson', "The Championship Finals begin as Tyson faces Gordo and Max faces Zeo. Can the BladeBreakers win both matches and repeat as champions, or will a 3rd and final match decide the outcome? Also, Zeo's secret will finally be revealed. All this occurs only on this episode of V-Force."),
    (2, 51): ('Destiny of the Final Battle', 'The finals between Zeo and Tyson begin, but with Zeo being revealed to be a cyborg can Tyson gain the endurance to win this battle and remain the world champion?'),
    (3, 1): ('New Kid in Town', 'Tyson is home training kids after winning his second championship when two new challengers arrive. What do they want with the World Champion?'),
    (3, 2): ('A Team Divided', 'The new rules of the World Championships cause changes to occur to the BladeBreakers, but will they be beneficial or harmful in the long run?'),
    (3, 3): ('Invitation to Battle', "With Ray and Max leaving the Bladebreakers to go to old teams, Jin decides to test Tyson, but when Ray ends up with the note he accepts Jin's challenge instead. Who will win between these two opponents?"),
    (3, 4): ('We Were Once Bladebreakers...', "With Max and Ray having quit the team, it's up to Kenny to keep the remaining Bladebreakers together. Will he succeed?"),
    (3, 5): ('A League of His Own', "Tyson must once again prove he's the best in Block A, but a Chameleon blade has a few surprises in store for him and Kenny. Who will win he first final?"),
    (3, 6): ("You're the Man, Kai!", "It's Kai versus Daichi in the block B final. Who will become Tyson's teammate, and what surprises does Jin of the Gale have for the team?"),
    (3, 7): ('Take Your Best Shot', "The BBA Revolution practices at Tyson's place while other qualifying matches are taking place, but who will the BBA Revolution end up facing? What surprises are in store for them?"),
    (3, 8): ('Roughing It', "The new BBA Revolution team will be complete when Kai finally makes his decision as to what team he's going to be on. How will this affect the World Championships?"),
    (3, 9): ('Swiped on the Streets', 'The World Championships are about to begin, but now that Kai has left the BBA Revolution, he must side with someone else. Who will that end up being? Also, how well will Daichi and Tyson get along? Find out in this episode of GRevolution.'),
    (3, 10): ("It's a Battle Royale", 'The BBA Revolution battles White Tiger X in the first match of the World Championships, but which man will end up with the bragging rights: Tyson or Ray?'),
    (3, 11): ('The Blame Game', "Tyson has been totally out of control since Kai transferred to the Blitzkreig Boys, not to mention the defeat to the White Tigers. He can't admit it was his fault and gets into an argument with Daichi. Meanwhile Barthez leads a new team in the ways of cheating. Can Tyson and the rest of the bladers handle these new chalengers?"),
    (3, 12): ('When In Rome, Let It Rip!', 'The White Tigers battle the Barthez Battalion in the first beystage in Rome for this years world tournament. Which side will prevail? Will Ray become 2-0 and the favorite to win it all, or will the Bartez men give him a run for his money?'),
    (3, 13): ("Kenny's Big Battle", 'Tyson is pulled from the battle against the Blitzkreig Boys and replaced by Kenny. What will this do to the BBA Revolution? Can Tyson get his ego under control finally?'),
    (3, 14): ('Picking Up the Pieces', "The Blitzkreig Boys are on a role and Tala defeats Kenny with a special attack! Next up to face Tala is Daichi. Even though Kenny lost to Tala, he has found a strategy to defeat him. But will Daichi use Kenny's plan for victory?"),
    (3, 15): ('Sleepless in Madrid', 'Lee of the White Tigers X suffers a lack of sleep due to nightmares that further emphasizes his mediocre performance lately. Tired and fragile, he pushes himself hard enough to cause his Galeon to run out of control during the match against F-Dynasty! Will Ray really forfeit the match in order to help his friend?'),
    (3, 16): ('Fire and Water', 'The Blitzkreg Boys battle the PBA All-Starz, and the truth behind the Barthez Battalion blades is revealed. What will this do to the World Championships?'),
    (3, 17): ('Same Old Dirty Tricks', "Finally, BBA Revolution faces off against the Barthez Battalion! Daichi faces off against Mathilda in the first match, but, following Barthez's evil plans, Mathilda reluctantly sacrifices her Beyblade to severly damage Daichi's Strata Dragoon, making it uncapable of fighting in a tie-breaker! Can Tyson win his match to achieve victory? And will Miguel finally make a stand to their cruel coach?"),
    (3, 18): ('Beyblade Like An Egyptian', 'The Barthez Battalion members must decide whether or not to cheat in their upcoming match against the Blitzkreig Boys, but which way will they decide?'),
    (3, 19): ('One For All . . . Free For All', 'The White Tigers battle the All-Starz, but can the All-Starz handle a team that works together when they are divided at times?'),
    (3, 20): ('Burdens of a Champion', 'The BBA Revolution must battle F-Dynasty in a tag match, but who will come out as the winners and continue into the next round.'),
    (3, 21): ('Under Pressure', "Ever since his loss against F Dynasty, Tyson falls to the pressures of being world champion, so much so that he embarrasses himself during a BBA Revolution interview! Can a match with Daichi help regain Tyson's true fighting spirit at last?"),
    (3, 22): ('Sibling Rivalry', 'Raul tries to convince Julia he should battle Matilda in their battle against Barthez Battalions. Who will go to the semi-finals to meet the Blitzkreig boys?'),
    (3, 23): ('Ray And Kai: The Ultimate Face-off...', 'Ray and Kai go head to head, and the winner gets to face Tyson, but who will end up prevailing between Dranzer and Driger?'),
    (3, 24): ('Down Under, Thunder', "Down in Australia, the BBA Revolution faces off against the PPB All-Starz. Everyone seems to believe that Rick will win in his match against Daichi, but the young boy is determined to prove to everyone that he will win! Can Daichi overcome Rick's Drop Rock attack so he can meet Tala of the Blitzkrieg Boys once again in the finals?"),
    (3, 25): ('Max Attacks', "The match between the BBA Revolution and the PPB All-Starz continues! Daichi has defeated Rick, so it's Max's turn to to battle with Tyson at last. Now that he has finally resolved his personal problems, will Tyson help the team move on to the next round? Will his Dragoon Galaxy even come out of this in one piece?!"),
    (3, 26): ('Familiar Faces', 'The final rounds take place back in Japan! Equipped with his new blade, Dragoon Galaxy Turbo, Tyson and the rest of BBA Revolution must face F Dynasty once more to reach the dominating team, the Blitzkrieg Boys. Will Tyson and Daichi manage to redeem themselves from their last defeat and best Raul and Julia?'),
    (3, 27): ('What a Blast', 'The whole city is watching the semi-finals match between BBA revolution and F-dynasty in a tag-team format. Tyson and Daichi want to dethrone the tag-team champions and intend to use some of the twins own moves to do so. The winner moves on to the finals where the Blitzkrieg Boys are waiting!'),
    (3, 28): ('Changing Gears', "The finals have finally arrived and BBA Revolution gets ready to face the Blitzkrieg Boys in a heated battle. But before that can happen, a routine check-up of Tyson's Beyblade turns up a faulty gear assembly, which needs to be repaired! Time is running out, and Daichi has to stretch out his match with Tala to give Kenny the time he needs to fix Dragoon!"),
    (3, 29): ('And Then There Were Two', 'Daichi and Tala have both been thrown from the dish at the same time, resulting in a tie game. Because they are in no condition for a rematch, Mr. Dickenson rules that the next match will determine the new tournament Champion. It all comes down to Kai and Tyson.'),
    (3, 30): ('Let The Games Begin... Again!', "It's the finals of the World Beyblading Championships and the final battle pits Kai against the defending world Champion, Tyson. The fight is incredibly intense and what's even more amazing, it looks like the two combatants are so evenly matched, there might not be a winner."),
    (3, 31): ('Runaway Daichi', 'The Beyblade World Championship finally concludes with BBA Revolution as the victorious team. However, an old wound opens in Daichi as he watches Tyson get all the attention once again. Will Daichi really leave the team for good?'),
    (3, 32): ('Beyblade Idol', "The BBA has been sold out, meaning Mr. Dickenson has no control over this mysterious new group, the Beyblade Entertainment Global Association: BEGA. Determined to find out what's going on, Tyson, Daichi, and Max challenge BEGA's mascot, the pop sensation, Ming Ming, to a battle! And, afterwards, Tyson meets a familiar face..."),
    (3, 33): ('Out of Their League', "Boris returns after two years of travelling, and explains what he has seen has changed him and inspired him to create BEGA, in an effort to convice the gang, he gives Tyson, Max, Daichi and kenny a tour of their facilities. Tyson finds out BEGA aren't slacking when he battles Crusher, who's motives may change Tyson's mind about Boris."),
    (3, 34): ('The Mysterious Mystel', 'At China, Ray and his White Tiger X teammates return to their usual life routine until the next World Championship until they encounter a strange and mysterious youth named Mystel. Will Ray be able to trust this stranger, especially after Mystel claims that Tyson is an official member of BEGA?!'),
    (3, 35): ('Pros and Ex-Cons', "Tyson, still thinking whether Boris has changed at all, is unsure about joining BEGA. Tala, Spencer, and Bryan go to confront Boris once again and shut his organization down for good. The Blitzkrieg Boys thrash their first three opponents, but Bryan and Spencer are beaten by Garland, who is one of BEGA's top bladers! Will he be too much for even Tala to handle?"),
    (3, 36): ('Boris, the Blade Stops Here', "In order to bring Boris' plan to a halt, Tala challenges Garland of Team Bega to a Beyblade match. But, Garland proves to be more than a match for him! Is Tala fighting a losing battle?"),
    (3, 37): ('The Bega Challenge', "Tyson accepts Boris' challenge to a five-on-five Beybattle for the future of the world of Beyblade. But, things are made worse when Kai joins BEGA and Hiro, as Jin of the Gale, becomes their new coach! It's up to Ray to bring Tyson back to his senses. But, since BEGA rules state that those who are not members cannot purchase new Beyblade parts, is this a battle they may end up regretting?"),
    (3, 38): ('Bega on the Rise', "While Tyson and the others find a way to make their own Beyblades, BEGA's influence continues to spread throughout the world. Hiro requests to coach BEGA's secret weapon, Brooklyn, but this young prodigy has a few surprises in store. Is it possible to be that powerful when Brooklyn never practiced a day in his life? Kai doesn't think so!"),
    (3, 39): ('Rebel Alliance', "In a miraculous turn of events, the past teams from the recent tournament, White Tiger X, PPB All-Starz, F-Dynasty, and Barthez Battalion joins Tyson and company in their battle against BEGA. With Emily and Miguel's help, Kenny manages to complete the first of the new Hard Metal Series of Beyblade, Dragoon Metal Storm! But, is it too much for even Tyson to control?!"),
    (3, 40): ('Back to Basics', 'Training camp continues as Tyson, Daichi, Ray, and Max strive to control their new HMS Beyblades. After several failures and humorous chase scenes, Tyson and the others must look into their hearts to find the answer of how to master complete control. It might even take them back to their childhood...'),
    (3, 41): ('And Justice-Five For All', "Under the pretext of gaining more supporters, BEGA holds a qualification tournament to decide the organization's five bladers they'll use in the Justice 5. Garland, Crusher, Ming Ming, and Mystel all secured their entries, and Kai ironically faces Brooklyn for the fifth spot. Will Kai defeat BEGA's secret weapon and get to face Tyson again in the end? Or will the mysterious Brooklyn demonstrate a skill unfathomable to all?"),
    (3, 42): ('When You Wish Upon A Star', 'Kai tries his best, but he is ultimately outmatched by Brooklyn. So, the BEGA team has been decided, and Tyson\'s team, the newly-named G-Revolutions, must act accordingly. While he buys a bit more time with ""Mister X"" as their fifth member, Tyson holds on to the wish that HE would join his team...'),
    (3, 43): ('Sing Ming Ming Sing!', 'For the first match, Daichi of Team G-Revolutions faces off against Ming Ming of Team Bega. But during the course of the match, the young pop star has won over the entire crowd, even Kenny! Can Daichi manage to overcome his most formidable opponent by far?'),
    (3, 44): ('Refuse to Lose', "The second match against BEGA begins as Ray does battle with the towering Crusher. Crusher's sister, Monica, is having her operation at the same moment, and he must win if he is to pay the expenses needed. Ray fights with the strong desire to save the future of all that is Beyblade, but will it be enough to overcome Crusher and his love for his sister?"),
    (3, 45): ('Max to the Maxx', 'Team G Revolution have two consecutive losses, so Max is given the pressure to win or face elimination. Can Rick give Max the encouragement he needs to face Mystel in the third match?'),
    (3, 46): ('The Return of Kai', "As Tyson trains intensively for his two consecutive matches against Brooklyn and Garland, a lifeless Kai visits Tala in the hospital and finds Dranzer MS beside him. The new Beyblade literally brings life back in Kai's eyes, and he desperately tries to gain control over it. Can F-Dynasty's coach, Romero, help him out so Kai will be able to rejoin his old team?"),
    (3, 47): ("Now You're Making Me Mad", "The fourth match begins with a great surprise. Kai has joined the G-Revolutions! And he demands a rematch with Brooklyn using his new blade, Dranzer MS. Will Kai just lose again to Brooklyn and Zeus' awesome dark powers? Or will his strong emotions turn the tide?"),
    (3, 48): ('Beyblading Spirit', "The fourth match between Kai and Brooklyn continues! Holding to the little faith he has left in his teammate, Tyson continues to cheer Kai on. As the battle wages on, with every move Brooklyn uses against him, Kai refuses to stay down! Brooklyn finally begins to lose composure to Kai's burning passion for Beyblade, but will the first win for G Revolutions come without a price?"),
    (3, 49): ('Principles of Victory', "It's a grudge match between the two team leaders, Tyson and Garland, in the fifth match! As the descendent of a family who dominates all the world's sports, Garland plans to uphold the family honor by winning this match. Will Tyson be able to stand up to this powerful Beyblader?"),
    (3, 50): ('Welcome to My Nightmare', "G Revolutions and the BEGA Bladers are now tied with two wins, two losses, and a draw. So, a sixth and final match has been announced! But, Boris seems to have other plans when he sends Crusher and Ming Ming to attack Tyson back at his home. This evil man's true colors are beginning to rise to the surface, and loyalty is torn between him and the BEGA Bladers. And what about Brooklyn? Ever since his defeat against Kai, his fate now walks an even darker path..."),
    (3, 51): ("Brooklyn's Back", "Finally, it's the tiebreaker match, Tyson versus Brooklyn! But, Brooklyn has changed for the worst after his defeat against Kai, and he completely submits to the seductive darkness of Zeus. This incredible power even threatens the entire world! Will Tyson be able to defeat Brooklyn at this level of intensity?!"),
    (3, 52): ('Beybattle for the Ages', "The match continues, and Brooklyn's dark powers may be too much for Tyson. But, with his old teammates behind him and with the power of Dragoon, Tyson will fight to the very end! And after this climatic battle, it WILL be the end..."),
}

GUNSMITH_CATS = [  # index = episode - 1: (name, synopsis)
    ("The Neutral Zone",
     "Gun experts Rally Vincent and Minnie May Hopkins, who run a Chicago gun shop, are pushed by "
     "ATF agent Bill Collins into breaking a gun-smuggling ring tied to underboss Jonathan Washington."),
    ("Swing High!",
     "Bill and the Gunsmith Cats have to work underground when a Russian hit woman starts wiping out evidence."),
    ("High Speed Edge",
     "The Gunsmith Cats are ready to get an award from Senator Haints but Bloody Pierce is ready for them."),
]

# Per-episode sub-titles the feed doesn't carry: (show, season, episode) -> sub-title
EPISODE_SUBS = {
    ("Homeless in Denton", 2, 5): "Fry St. Fair '06",
}

# Eel shows the feed sends with no episode number: fetch a SHOW-level synopsis
# (TMDB -> TVmaze -> TVDB, then OMDb). Value = the name to try on OMDb/IMDb if it differs.
# The feed sends films as "<Franchise> Movie" + sub-title "<Film> (YYYY)" + a fake S/E.
# Shown film-style instead: "<Franchise>: <Film> (YYYY)", no S/E, TMDB movie lookup.
# FILM_CANON fixes known films to TMDB's exact title (keyword in the sub-title -> canonical).
_FILM_FRANCHISE = re.compile(r"^(.*\S)\s+(?:Movie|OVA)$", re.I)   # "DBZ Movie"/"DBZ OVA" + "<Film> (YYYY)"
FILM_CANON = {
    "tree of might": "Dragon Ball Z: The Tree of Might (1990)",
    "bardock":       "Dragon Ball Z: Bardock - The Father of Goku (1990)",
}

# Episode names the feed spells differently from TVmaze/TVDB: (show, feed name) -> lookup name
EP_NAME_ALIAS = {
    ("Beavis and Butt-Head", "PTA"): "P.T.A.",
    ("Beavis and Butt-Head", "The Final Judgment of Beavis"): "The Final Judgement of Beavis",
}

EEL_SHOW_LOOKUP = {
    "The Super Milk-Chan Show": "The Super Milk Chan Show",      # IMDb spelling
    "Mighty Mouse: The New Adventures (1987)": None,
    # episodic shows whose episode text is missing or non-English in the DBs -> show synopsis
    "Space Goofs": None,
    "Funky Cops": None,
    "Free for All (2003)": None,
    # no episode text in any DB (Nov 27 2026 check) -> show-level synopsis (TMDB/TVmaze/TVDB, then IMDb)
    "1000 Ways to Die": None,
    "Storm Hawks": None,
    "Beyblade": None,
}

# Multi-part specials the feed sends as "<Title>: Part N" / "<Title> (N)" with no S/E:
# treat Part N as S01 E N so the episode name + synopsis come from the DBs.
PART_AS_EPISODE = {"This Is America, Charlie Brown"}
_PART_TAIL = re.compile(r"^(.*?)\s*(?::\s*Part\s+(\d{1,2})|\(\s*(?:Part\s+)?(\d{1,2})\s*\)|\s+Part\s+(\d{1,2}))\s*$", re.I)

# Non-English overview guard: TMDB falls back to the original language (Space Goofs and
# Funky Cops come back in French). Such text is skipped so the next source is tried.
_FOREIGN_WORDS = {"le", "la", "les", "des", "du", "de", "une", "un", "est", "et", "dans", "pour",
                  "qui", "sur", "pas", "avec", "sont", "au", "aux", "il", "elle", "ils", "leur",
                  "en", "à", "ne", "se", "ce", "mais", "d", "l", "être", "très", "lui"}
def _looks_foreign(text):
    words = re.findall(r"[a-zà-ÿ]+", (text or "").lower())
    if len(words) < 6:
        return False
    return sum(1 for w in words if w in _FOREIGN_WORDS) / len(words) > 0.15
_PLACEHOLDER_EP = re.compile(r"^[ÉE]pisod[ei]o?\s*#?\d+(?:\.\d+)?$", re.I)   # also OMDb's "Episode #1.5"   # "Episode 23"/"Épisode 4" = no real name

# ── Part-marker standardization (guardrail across all 3 Eel channels) ──────
# Normalize two-parter markers to "Title: Part N": "(1)/(2)", "(Part One)",
# "City of Stone: Part Four", bare " Part Two" -> ": Part 1/2/4...". Conservative:
# acts only on an explicit "Part" keyword or a trailing 1-2 digit "(N)"; never touches
# "Mock 5", "D2", or 4-digit years like "(1995)". Applied to title AND sub-title.
_WORDNUM = {"one":1,"two":2,"three":3,"four":4,"five":5,"six":6,"seven":7,"eight":8,"nine":9,"ten":10}
def _wordnum(w):
    w = w.strip().lower()
    return _WORDNUM.get(w, int(w) if w.isdigit() else None)
def norm_parts(title):
    if not title:
        return title
    t = title.rstrip()
    def mk(base, n):
        return base.rstrip().rstrip(":,").rstrip() + f": Part {n}"
    m = re.search(r'\s*\(\s*Part\s+([A-Za-z]+|\d{1,2})\s*\)\s*$', t, re.I)   # "(Part One)"/"(Part 1)"
    if m and _wordnum(m.group(1)): return mk(t[:m.start()], _wordnum(m.group(1)))
    m = re.search(r'\s*\(\s*(\d{1,2})\s*\)\s*$', t)                          # "(1)"/"(2)"
    if m: return mk(t[:m.start()], int(m.group(1)))
    m = re.search(r'\s*:?\s*Part\s+([A-Za-z]+|\d{1,2})\s*$', t, re.I)        # ": Part X"/" Part X"
    if m and _wordnum(m.group(1)): return mk(t[:m.start()], _wordnum(m.group(1)))
    return t

# Normalize a title/segment name to a match key (mirrors build_guide.py _norm) so the
# feed's TMDB-sourced names resolve to the authoritative guide regardless of case,
# punctuation, accents, "&"/"and", or part-marker spelling ("(1)" == ": Part One").
def _guide_norm(s):
    s = unicodedata.normalize("NFKD", s or "")
    s = "".join(c for c in s if not unicodedata.combining(c))
    s = s.lower().replace("&", "and")
    s = re.sub(r'\bpart\s+(one|two|three|four|five|six|seven|eight|nine|ten)\b',
               lambda m: "part" + str(_WORDNUM[m.group(1)]), s)
    s = re.sub(r'[:\-]?\s*part\s*(\d{1,2})\b', lambda m: " part" + m.group(1), s)
    s = re.sub(r'\(\s*(\d{1,2})\s*\)\s*$', lambda m: " part" + m.group(1), s.strip())
    return re.sub(r'[^a-z0-9]', '', s)

# ── Per-show air-order override guide ──────────────────────────────────────
# Some Eel/Fizz shows are numbered by the feed in its own (broadcast) order, which
# the metadata DBs don't share (TMDB/IMDb use production/DVD order), so a DB lookup
# by the feed number lands on the wrong episode. fizz_guide.json maps the feed
# straight to the real episode, built OFFLINE from authoritative guides:
#   { "<Show>": {"mode": "absolute"|"se"|"name", "eps": <list|dict>} }
#   - mode "absolute": eps is a list indexed by the feed's absolute episode number
#     (feed_ep-1). Batman: The Animated Series — Wikipedia broadcast order + Wiki
#     S/E, synopsis from IMDb (matched by title), titles normalized "X: Part N".
#   - mode "se": eps is a dict keyed "<season>.<episode>". Garfield and Friends —
#     feed S/E already matches IMDb; segments joined " / ", per-segment IMDb
#     synopsis " / "-joined where IMDb labels them, else the full episode synopsis.
#   - mode "name": eps is a dict keyed by _guide_norm(<episode or segment name>). Used
#     when the feed numbers the show on TMDB's grid but TMDB/IMDb disagree on the
#     NUMBERING (so a by-number key would misalign). We resolve the item's name (the
#     feed's sub-title, else the TMDB episode name for the feed's S/E) and match THAT.
#     The displayed S/E is left as the feed's. Gargoyles (non-segmented: name -> that
#     episode's IMDb title+synopsis, Part-normalized). Dexter's Laboratory / Rocko's
#     Modern Life (SEGMENTED: the feed labels each half-hour slot with one TMDB segment;
#     every segment name maps to its IMDb HALF-HOUR -> all segment titles joined " / "
#     plus the half-hour's IMDb synopsis, Garfield-style). Non-matches fall through to
#     the normal TMDB/TVmaze/TVDB path, so the guide can only improve, never corrupt.
FIZZ_GUIDE_FILE = "fizz_guide.json"
def load_fizz_guide():
    try:
        with open(FIZZ_GUIDE_FILE, encoding="utf-8") as f:
            return json.load(f)
    except Exception as e:
        print(f"  fizz guide: {FIZZ_GUIDE_FILE} not loaded ({e})")
        return {}
FIZZ_GUIDE = load_fizz_guide()

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
P_TFRONT_PART = re.compile(r'^T\d{2,4}[a-z]\s+(\S.*)$', re.I)   # "T107b Tenchi Muyo! Mihoshi Special": in-between special, no real S/E

def _digits_to_se(d, show):
    if show.strip().lower() in ABSOLUTE_SHOWS: return 1, int(d)
    if len(d) == 2: return 1, int(d)
    if len(d) == 3: return (1, int(d[1:])) if d[0] == '0' else (int(d[0]), int(d[1:]))
    if len(d) == 4: return int(d[:2]), int(d[2:])
    return 1, int(d)

def _clean(s):
    s = re.sub(r'^[\s_\-–—]+|[\s_\-–—]+$', '', s.strip())   # incl. en/em dashes
    return re.sub(r'\s{2,}', ' ', s).strip()

def _rename(title):
    m = YEAR_END.search(title)
    yr = " " + m.group(1) if m else ""
    base = title[:m.start()].strip() if m else title
    if base in RENAMES:
        base = RENAMES[base]
        if YEAR_END.search(base):
            yr = ""              # canonical already carries its year: no "(1987) (1987)"
    else:
        for rx, canon in REGEX_RENAMES:
            if rx.match(base):
                base = canon
                yr = ""          # canonical already carries any year it needs
                break
    if base in DROP_YEAR:
        yr = ""                  # strip the source year for these titles
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
            else:
                # the episode name itself may contain " - " ("SOUTH PARK 316 - Are you there
                # God - It's me, Jesus"): find the earliest "<Show> <3-4 digits>" prefix.
                for i in range(1, len(segs) - 1):
                    mm = re.search(r'^(.*\S)\s+(\d{3,4})$', " - ".join(segs[:i]).strip())
                    if mm:
                        season, ep = _digits_to_se(mm.group(2), mm.group(1))
                        title = _clean(mm.group(1)); subtitle = " - ".join(segs[i:]).strip()
                        break
                else:
                    title = _clean(" - ".join(segs[:-1]))
    else:
        c = peel(t)
        if c: title, season, ep = _clean(c[0]), c[1], c[2]
        else:
            fp = P_TFRONT_PART.match(t)
            fm = P_TFRONT.match(t)
            if fp:
                title = _clean(fp.group(1))                     # drop the code, keep the title, no S/E
            elif fm:
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
SHOW_TMDB_OVERRIDES = {"DuckTales (1987)": 720}   # TMDB id 720 = the 1987 series, not the 2017 reboot

_QYEAR = re.compile(r'\s*\(((?:19|20)\d\d)\)\s*$')
_tmdb_session = requests.Session()

def load_desc_cache():
    try:
        with open(DESC_CACHE_FILE, encoding="utf-8") as f:
            c = json.load(f)
            for k in ("shows","episodes","tvmaze_shows","tvmaze_episodes","tmdb_seasons",
                      "tvmaze_eplist","tvdb_shows","tvdb_episodes",
                      "tvmaze_namemap","tvdb_namemap","tmdb_movies","show_syn"):
                c.setdefault(k, {})
            if not c.get("_tvdb_v2"):                    # refresh TVDB layer once (/eng + slug overrides)
                c["tvdb_shows"] = {}; c["tvdb_episodes"] = {}; c["_tvdb_v2"] = True
            if not c.get("_meta_v3"):                    # refresh episode caches once to capture episode NAMES
                for _k in ("episodes","tvmaze_episodes","tvdb_episodes","tvmaze_eplist"): c[_k] = {}
                c["_meta_v3"] = True
            if not c.get("_tvdb_v3"):                    # drop TVDB "first episode" fallbacks (DBZ/Tenchi bug)
                c["tvdb_episodes"] = {}; c["_tvdb_v3"] = True
            return c
    except Exception:
        return {"shows": {}, "episodes": {}, "tvmaze_shows": {}, "tvmaze_episodes": {},
                "tmdb_seasons": {}, "tvmaze_eplist": {}, "tvdb_shows": {}, "tvdb_episodes": {},
                "tvmaze_namemap": {}, "tvdb_namemap": {}, "tmdb_movies": {}, "show_syn": {}}

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
            # exact match only: falling back to eps[0] stamped one special's name/synopsis on
            # every missing number (DBZ E40-45 "Christmas Tree of Might", Tenchi Universe S2)
            m = next((e for e in eps if e.get("seasonNumber") == season and e.get("number") == ep), None)
            if m is None:
                continue
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
        if o and not ov and not _looks_foreign(o): ov = o
        if n and not nm and not _PLACEHOLDER_EP.match(n.strip()): nm = n
        return bool(ov and nm)
    if take(_tmdb_meta(show, season, ep, cache)):                 return ov, nm
    if OMDB_KEY and take(_omdb_episode(show, season, ep, cache)):     return ov, nm   # IMDb, 2nd
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

# Fixed descriptions for Whiplash-feed programmes that arrive without one (by title).
WL_FIXED_DESC = {
    # nightly off-air gap on the whiplash channel
    "OFF-AIR": "I AM NOT AWAKE RIGHT NOW"
               "\n\n"
               "I AM GETTING SOME BEAUTY SLEEP"
               "\n\n"
               "I'LL BE BACK SOON",
}

def _add_fixed_desc(prog):
    """Give a feed programme a fixed <desc> (placed right after title/sub-title) if it has none."""
    text = WL_FIXED_DESC.get((prog.findtext("title") or "").strip())
    if not text or prog.find("desc") is not None:
        return
    d = ET.Element("desc", {"lang": "en"}); d.text = text
    pos = 0
    for i, ch in enumerate(list(prog)):
        if ch.tag in ("title", "sub-title"): pos = i + 1
    prog.insert(pos, d)

# Off-air fillers in the Whiplash feed: consecutive filler slots are merged, then
# retitled / described. "block_h" splits the merged run into blocks of that many hours
# (aligned to 00:00/12:00 UTC for 12); None keeps one block per run.
WL_FILLER_MERGE = {
    "whiplashwindowtv": {"match": "programmes start at 6am",
                         "title": "Programmes start at 6AM",       # British channel: British spelling
                         "desc":  "We'll be back at 6AM.",
                         "block_h": None},
    "whiplashcinema":   {"match": "programming has been suspended",
                         "title": None,                     # keep feed title
                         "desc":  "Programming on Whiplash Cinema is currently suspended."
                                  "\n\n"
                                  "We hope to return in a hopefully much improved state soon.",
                         "block_h": 12},
}

def _wl_t(s):  return datetime.strptime(s[:14], "%Y%m%d%H%M%S")
def _wl_s(dt): return dt.strftime("%Y%m%d%H%M%S") + " +0000"

def _merge_fillers(local_id, progs):
    cfg = WL_FILLER_MERGE.get(local_id)
    if not cfg:
        return progs
    is_fill = lambda p: cfg["match"] in (p.findtext("title") or "").lower()
    out, i = [], 0
    while i < len(progs):
        if not is_fill(progs[i]):
            out.append(progs[i]); i += 1; continue
        j = i
        while j + 1 < len(progs) and is_fill(progs[j + 1]) and progs[j + 1].get("start") == progs[j].get("stop"):
            j += 1
        a, b = _wl_t(progs[i].get("start")), _wl_t(progs[j].get("stop"))
        title = cfg["title"] or (progs[i].findtext("title") or "").strip()
        cuts = [a]
        if cfg["block_h"]:
            step = timedelta(hours=cfg["block_h"])
            nxt = a.replace(hour=0, minute=0, second=0) + step
            while nxt <= a: nxt += step
            while nxt < b: cuts.append(nxt); nxt += step
        cuts.append(b)
        for x, y in zip(cuts, cuts[1:]):
            np = ET.Element("programme", {"start": _wl_s(x), "stop": _wl_s(y), "channel": local_id})
            ET.SubElement(np, "title", {"lang": "en"}).text = title
            ET.SubElement(np, "desc", {"lang": "en"}).text = cfg["desc"]
            out.append(np)
        i = j + 1
    return out

def copy_whiplash(tv, root):
    for src_id, (local_id, _) in WL_CHANNEL_MAP.items():
        progs = []
        for prog in root.findall("programme"):
            if prog.get("channel") != src_id: continue
            np = ET.fromstring(ET.tostring(prog)); np.set("channel", local_id)
            _strip_local_images(np); _space_onscreen(np); _add_fixed_desc(np)
            progs.append(np)
        n0 = len(progs)
        progs = _merge_fillers(local_id, progs)
        for np in progs: tv.append(np)
        if progs:
            extra = f" (fillers merged from {n0})" if len(progs) != n0 else ""
            print(f"  {local_id}: {len(progs)} programmes{extra}")

def _guide_get(gdef, name):
    """Look a feed episode name up in a name-mode guide. A sub-title that packs several
    segments ("A Great Day; Follow Me") is split on ';' and each part looked up; the
    result joins titles and descriptions with " / " and takes the first segment's S/E."""
    eps = gdef["eps"]
    hit = eps.get(_guide_norm(name))
    if hit or ";" not in name:
        return hit
    parts = [x.strip() for x in name.split(";") if x.strip()]
    found = [eps.get(_guide_norm(x)) for x in parts]
    if not all(found):
        return None
    out = {"title": " / ".join(f.get("title") or x for f, x in zip(found, parts)),
           "desc": " / ".join(f["desc"] for f in found if f.get("desc")) or None}
    if found[0].get("se"):
        out["se"] = found[0]["se"]
        out["se_all"] = [f.get("se") for f in found]   # every segment's S/E -> "E14+E16"
    return out

def build_eel(tv, root, cache):
    got_desc = got_sub = 0
    # Resolve each configured Eel channel to the source id present in THIS feed.
    # Prefer the configured id; if it has vanished (feed renumbered it), auto-switch
    # to whichever DECLARED channel now carries the matching display-name, keyed on
    # the stable tvg-id. Undeclared "orphan" programme ids are ignored.
    declared = {c.get("id"): (c.findtext("display-name") or "") for c in root.findall("channel")}
    # ids that actually carry programmes. The feed's channel declarations flip between
    # renumbered ids (Nov 27 2026: it declared the stale C121.244 "E Toons" while the live
    # eToons grid sat under the UNdeclared C122.245), so a configured id counts as present
    # if it has programmes, declared or not.
    with_progs = {p.get("channel") for p in root.findall("programme")}
    name2local = {_norm_chan_name(disp): loc for loc, disp in EEL_CHANNEL_MAP.values()}
    for _alias, _loc in EEL_NAME_ALIASES.items():
        name2local[_norm_chan_name(_alias)] = _loc
    resolved = {}   # src_id_in_feed -> (local_id, display)
    # Content check for Toon Diggity: the feed keeps a stale twin (Nov 27 2026: declared
    # C121.244 = old Cartoon Shuffle grid, undeclared C122.245 = live eToons grid). Whichever
    # configured id carries the eToons segment titles wins, whatever the declarations say.
    _seg = {"Terry Toons", "Columbia Cavalcade", "Universal Union", "Paramount Potluck", "MGM Gems"}
    _td_ids = [cid for cid, (loc, _) in EEL_CHANNEL_MAP.items() if loc == "toon-diggity"]
    _td_live = [cid for cid in _td_ids if any((p.findtext("title") or "").strip() in _seg
                for p in root.findall("programme") if p.get("channel") == cid)]
    if len(_td_live) > 1:                # both carry it (Nov 27 2026 "ID fixed"): trust the declared one
        _decl = [cid for cid in _td_live if cid in declared]
        _td_live = _decl or _td_live[-1:]
    if len(_td_live) == 1:
        resolved[_td_live[0]] = EEL_CHANNEL_MAP[_td_live[0]]
    # newest ids are listed last, so walk the map backwards: if the feed still declares an
    # old id next to the new one, the newest wins and the channel is never doubled
    for want_id, (local_id, display) in reversed(list(EEL_CHANNEL_MAP.items())):
        if local_id in {loc for loc, _ in resolved.values()}:
            continue
        if want_id in declared or want_id in with_progs:
            resolved[want_id] = (local_id, display)
            if want_id not in declared:
                print(f"  NOTE: Eel '{display}' using {want_id} (has programmes but the feed "
                      f"doesn't declare it)")
            continue
        alt = next((cid for cid, cname in declared.items()
                    if cid not in EEL_CHANNEL_MAP and name2local.get(_norm_chan_name(cname)) == local_id), None)
        if alt:
            resolved[alt] = (local_id, display)
            print(f"  NOTE: Eel '{display}' source id changed {want_id} -> {alt} "
                  f"(auto-matched by display-name; update EEL_CHANNEL_MAP to silence)")
        # (no match by id or name: handled by the last-resort pass below)
    # Last resort for a rebrand we have no alias for yet: if a channel is still unresolved and
    # exactly ONE declared feed channel is unclaimed, that must be it (the feed carries only
    # Eel / Fizz / Toon Diggity). Logged loudly so the alias can be added.
    got_local = {loc for loc, _ in resolved.values()}
    for want_id, (local_id, display) in EEL_CHANNEL_MAP.items():
        if local_id in got_local:
            continue
        got_local.add(local_id)          # one decision (and one log line) per channel
        free = [cid for cid in declared if cid not in resolved and cid not in EEL_CHANNEL_MAP]
        if len(free) == 1:
            resolved[free[0]] = (local_id, display); got_local.add(local_id)
            print(f"  NOTE: Eel '{display}' not found by id or name; using the only unclaimed feed "
                  f"channel {free[0]} ('{declared[free[0]]}'). Add its name to EEL_NAME_ALIASES.")
        else:
            print(f"  WARNING: Eel '{display}' not found by id or name ({len(free)} unclaimed feed "
                  f"channels) -> this channel will be EMPTY this run")
    _order = {loc: i for i, (loc, _) in enumerate(EEL_CHANNEL_MAP.values())}
    resolved = dict(sorted(resolved.items(), key=lambda kv: _order.get(kv[1][0], 99)))   # Eel, Fizz, Toon Diggity
    for src_id, (local_id, _) in resolved.items():
        n = 0
        for prog in root.findall("programme"):
            if prog.get("channel") != src_id: continue
            raw_title = (prog.findtext("title") or "").strip()
            title, sub, season, ep, ep_end = parse_title(raw_title)
            if sub: sub = _clean(sub) or None                                 # "– Misfit Love" -> "Misfit Love"
            title = _rename(_decap(title))                                    # BLOCK CAPS -> Title Case
            if season is not None and season in SEASON_REMAP.get(title, {}):
                season = SEASON_REMAP[title][season]                          # T225 Tenchi Universe -> S01 E25
            _jm = re.match(r"^(Dragon Ball(?: Z)?)\s+(\d{1,3})\s*[-+&/]\s*(\d{1,3})$", raw_title.strip(), re.I)
            if _jm:                              # joint slot "Dragon Ball Z 140-141" (absolute numbers)
                title, sub, season = _jm.group(1).title().replace("Z", "Z"), None, 1
                ep, ep_end = int(_jm.group(2)), int(_jm.group(3))
            pinned = False                       # title/sub/S-E/desc fully set from a built-in list
            _jse = None                          # joint-slot S/E list from a built-in list
            if title == "Tenchi Universe" and ep and 1 <= ep <= len(TENCHI_UNIVERSE):
                _arc, season, ep, sub, _syn = TENCHI_UNIVERSE[ep - 1]
                title, ep_end, pinned = f"Tenchi Universe - {_arc}", None, True
            elif title == "Dragon Ball Z" and ep and season in (None, 1) and 1 <= ep <= len(DRAGON_BALL_Z):
                # absolute 1-291 -> TMDB saga S/E; a joint slot ("140-141") joins names/synopses with " / "
                _es = [DRAGON_BALL_Z[i - 1] for i in range(ep, (ep_end or ep) + 1) if i <= len(DRAGON_BALL_Z)]
                title = f"Dragon Ball Z - {_es[0][2]}"
                season, ep = _es[0][0], _es[0][1]
                sub = " / ".join(e[3] for e in _es); _syn = " / ".join(e[4] for e in _es)
                ep_end, _jse = _joint_nums([(e[0], e[1]) for e in _es])
                pinned = True
            elif title == "Dragon Ball" and ep and season in (None, 1) and 1 <= ep <= len(DRAGON_BALL):
                _es = [(1, i) + DRAGON_BALL[i - 1] for i in range(ep, (ep_end or ep) + 1) if i <= len(DRAGON_BALL)]
                title = f"Dragon Ball (1986) - {_es[0][2]}"     # the 1986 series, absolute 1-153, one season
                season, ep = 1, _es[0][1]
                sub = " / ".join(e[3] for e in _es); _syn = " / ".join(e[4] for e in _es)
                ep_end, _jse = _joint_nums([(e[0], e[1]) for e in _es])
                pinned = True
            elif title == "Gunsmith Cats" and ep and 1 <= ep <= len(GUNSMITH_CATS):
                sub, _syn = GUNSMITH_CATS[ep - 1]
                season, ep_end, pinned = 1, None, True
            elif title == "DuckTales (1987)" and ep and (season or 1, ep) in DUCKTALES:
                season = season or 1                     # feed S/E == IMDb S/E (TMDB's names run off)
                sub, _syn = DUCKTALES[(season, ep)]
                ep_end, pinned = None, True
            elif title == "The Charlie Brown and Snoopy Show" and ep and (season or 1, ep) in CHARLIE_BROWN_SNOOPY:
                season = season or 1                     # feed S/E == IMDb S/E
                sub, _syn = CHARLIE_BROWN_SNOOPY[(season, ep)]
                ep_end, pinned = None, True
            elif title == "Beyblade" and ep and (season or 1, ep) in BEYBLADE:
                season = season or 1                     # the 2001 original (Tyson/Dragoon), TMDB per season
                sub, _syn = BEYBLADE[(season, ep)]
                ep_end, pinned = None, True
            elif title == "Starcade":                     # show-level only: no sub-title, no S/E
                sub, season, ep, ep_end, _syn, pinned = None, None, None, None, FIXED_DESC["Starcade"], True
            elif title == "Storm Hawks" and ep:
                _abs = ep if season in (None, 1) else 26 * (season - 1) + ep   # feed sends absolute "47"
                if 1 <= _abs <= len(STORM_HAWKS):
                    season, ep, sub, _syn = STORM_HAWKS[_abs - 1]
                    ep_end = None
                    pinned = _syn is not None   # no episode text -> normal lookups fill it (S/E now right)
            elif title == "1000 Ways to Die" and sub:
                _w = WAYS_TO_DIE_1000.get(_guide_norm(sub))
                if _w:
                    sub, _syn = _w
                    pinned = True                        # S/E stays the feed's
            title = _eel_segment_rename(title, prog.get("start"), local_id)   # time/channel-based renames
            if season is None:                    # "This Is America, Charlie Brown: Part 2" -> S01 E02
                pm = _PART_TAIL.match(f"{title}: {sub}" if sub else title)
                if pm and pm.group(1) in PART_AS_EPISODE:
                    title, sub = pm.group(1), None
                    season, ep = 1, int(pm.group(2) or pm.group(3) or pm.group(4))
            if sub and season is None:            # "Show" + "Special" split by the feed -> one known title
                _j = f"{title}: {sub}"
                _r = _rename(_j)
                if _r != _j or _r in FIXED_DESC:
                    title, sub = _r, None
            fm = _FILM_FRANCHISE.match(title)
            if fm and sub:
                yr = re.search(r"\((?:19|20)\d\d\)", sub) or re.search(r"\((?:19|20)\d\d\)", raw_title)
                if yr:
                    film = re.sub(r"\s*\((?:19|20)\d\d\)\s*", " ", sub).strip()
                    # joint parts in one slot: "(1-2)", "(1 & 2)", "Parts 1 and 2", "Part 1 / Part 2"
                    _pj = re.search(r"(?:\bparts?\s*|\()(\d)\s*(?:-|&|\+|and|/\s*part)\s*(\d)\)?\s*$", film, re.I)
                    _pt = None if _pj else re.search(r"(?:\bpart\s*|\()(\d)\)?\s*$", film, re.I)   # "(2)" / "Part 2"
                    if _pj or _pt: film = film[:(_pj or _pt).start()].strip(" :-")
                    _sp = next((x for x in DBZ_SPECIALS if x[0] in film.lower()), None)
                    canon = _sp[1] if _sp else next((v for k, v in FILM_CANON.items() if k in film.lower()), None)
                    title = canon or f"{fm.group(1)}: {film} {yr.group(0)}"
                    sub = (f"Part {_pj.group(1)} / Part {_pj.group(2)}" if _pj
                           else f"Part {_pt.group(1)}" if _pt else None)
                    season, ep, ep_end = None, None, None
                    if _sp and _sp[2]:
                        _syn, pinned = _sp[2], True
            desc = _syn if pinned else None
            joint_se = _jse          # [[s,e],...] for a joint (multi-segment) episode
            # Per-show override guide (feed numbers the show in an order the DBs don't share).
            #   mode "absolute": index by the feed's absolute episode number (Batman).
            #   mode "se":       key by the feed's season.episode (Garfield; feed S/E == guide S/E).
            gentry = None
            gdef = FIZZ_GUIDE.get(title)
            if gdef and ep is not None:
                mode = gdef.get("mode")
                if mode == "absolute":
                    lst = gdef["eps"]
                    if 1 <= ep <= len(lst):
                        gentry = lst[ep - 1]
                        season, ep = gentry["se"]
                        sub = gentry.get("title") or sub
                elif mode == "se" and season is not None:
                    gentry = gdef["eps"].get(f"{season}.{ep}")
                    if gentry:
                        sub = gentry.get("title") or sub   # season/ep unchanged (feed matches guide)
                elif mode == "name":
                    # resolve the item's episode/segment name, then match by name (feed
                    # numbers on TMDB's grid but the NUMBERING differs from IMDb's).
                    look = sub
                    if not look and season is not None:
                        _d, look = episode_meta(title, season, ep, cache)
                    if look:
                        gentry = _guide_get(gdef, look)
                        if gentry:
                            sub = gentry.get("title") or sub   # S/E left as the feed's
                            if gdef.get("renumber") and gentry.get("se"):
                                season, ep = gentry["se"]       # feed numbering unreliable -> guide's
            elif gdef and gdef.get("mode") == "name" and ep is None and sub:
                # name-mode show with no parsed number but a feed sub-title -> match on it
                gentry = _guide_get(gdef, sub)
                if gentry:
                    sub = gentry.get("title") or sub
                    if gdef.get("renumber") and gentry.get("se"):
                        season, ep = gentry["se"]
            if gentry is not None:
                desc = gentry.get("desc") or None
                if gdef.get("renumber") and gentry.get("se_all") and all(gentry["se_all"]):
                    joint_se = gentry["se_all"]
            elif season is None and sub:                # have episode name, no number -> match it
                season, ep = _name_to_se(title, EP_NAME_ALIAS.get((title, sub), sub), cache)
            if gentry is None and season is not None and not pinned:
                desc, epname = episode_meta(title, season, ep, cache)
                if not sub and epname:                 # fill missing episode name from metadata
                    sub = epname; got_sub += 1
            if season is not None and (title, season, ep) in EPISODE_SUBS:
                sub = EPISODE_SUBS[(title, season, ep)]
            if desc is None and title in FIXED_DESC:    # fixed desc for block/filler programmes
                desc = FIXED_DESC[title]
            if desc is None and title in EEL_SHOW_LOOKUP:   # show-level synopsis, IMDb spelling as backup
                desc = _show_overview_db(title, cache) or None
                if not desc and OMDB_KEY:
                    desc = _omdb_plot(EEL_SHOW_LOOKUP[title] or title, cache, "series") or None
            # Movie fallback: non-episodic entries carrying a (YYYY) in the title or
            # sub-title are films (e.g. "American History X (1998)", or "Teen Titans" +
            # "Trouble in Tokyo (2006)"). Look them up as MOVIES on TMDB. Display title
            # and sub-title are left exactly as-is; only the description is filled.
            if desc is None and season is None and title not in FIXED_DESC and not gdef and TMDB_KEY:
                mq = f"{title}: {sub}" if sub else title
                if re.search(r"\((?:19|20)\d\d\)", mq):
                    _my, _mov = _movie_meta(mq, cache)
                    if _mov:
                        desc = _mov; got_desc += 1
            # Part-marker guardrail (runs AFTER movie detection so a "(YYYY)" is untouched):
            # standardize "(1)/(2)"/"(Part One)"/": Part Four" -> ": Part N" on every channel.
            title = norm_parts(title)
            if sub and not re.fullmatch(r"Part \d+(?: / Part \d+)*", sub):   # "Part 1 / Part 2" is final
                sub = norm_parts(sub).lstrip(": ") or None   # bare "Part 2" sub stays "Part 2"
            np = ET.Element("programme", {k: prog.get(k) for k in prog.keys()})
            np.set("channel", local_id)
            ET.SubElement(np, "title", {"lang": "en"}).text = title
            if sub: ET.SubElement(np, "sub-title", {"lang": "en"}).text = sub
            if desc:
                ET.SubElement(np, "desc", {"lang": "en"}).text = desc
                got_desc += 1
            if season is not None:
                onscr = f"S{season:02d} E{ep:02d}" + (f"-E{ep_end:02d}" if ep_end else "")
                if joint_se and len(joint_se) > 1:     # joint episode: "S07 E14+E16"
                    onscr = f"S{joint_se[0][0]:02d} E{joint_se[0][1]:02d}" + "".join(
                        f"+E{e:02d}" if s_ == joint_se[0][0] else f"+S{s_:02d} E{e:02d}"
                        for s_, e in joint_se[1:])
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
    # year-tagged keys carry a "v2" so titles cached as misses under the old,
    # stricter vote rule get one fresh lookup
    key = clean.lower() + (f"|{year}|v2" if year else "")
    if key in cache["tmdb_movies"]:
        rec = cache["tmdb_movies"][key]
        return (rec["y"], rec["o"]) if rec else (None, None)
    params = {"query": clean}
    if year: params["year"] = year
    data = _tmdb_get("/search/movie", **params) or {}
    rec = None
    for res in (data.get("results") or [])[:5]:
        rd = res.get("release_date") or ""
        votes = res.get("vote_count") or 0
        if _norm(res.get("title")) != _norm(clean):
            continue
        if year:
            # a year in the feed is strong evidence: accept small titles (TV specials like
            # the Peanuts ones have only a handful of votes) if TMDB's year is within 1
            if not (rd[:4].isdigit() and abs(int(rd[:4]) - int(year)) <= 1 and votes >= 3):
                continue
        elif votes < 50:
            continue
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

# ── US-Central fixed-weekly-lineup channels (CCN, NickPicks): show-level synopses ──
# Each schedule file is {weekday: [[start_min, stop_min, "Title"], ...]} in Central local time.
# Schedules repeat weekly; each channel has its own exclusive end horizon.
WEEKLY_START = datetime(2026, 9, 30)    # first Central date to generate (covers "now")

CCN_OUTPUT     = "CCN.xml"
CCN_ID         = "CartoonCartoonsNetwork"
CCN_NAME       = "Cartoon Cartoons Network"
CCN_LOGO       = "https://i.imgur.com/CaeVZxd.png"
CCN_SCHED_FILE = "ccn_schedule.json"
CCN_DAYS       = 30                     # rolling: yesterday -> +30 days, rebuilt every run
# The CCN website keeps its weekly lineup inside its Owncast custom script, as a plain
# {Day: {"HH:MM": "Show"}} object (US Central, 30-min slots). We read it every run, so
# the guide follows the site; ccn_schedule.json is refreshed from it and is the fallback.
CCN_LIVE_URL   = "https://cartooncartoons.thatsoretro.com/customjavascript"
CCN_RENAMES    = {                       # site title -> our guide title
    "Cartoon Theatre": "Cartoon Theater",
    "DragonBall": "Dragon Ball",
    "DragonBall Z": "Dragon Ball Z",
    "Fullmetal Alchemist Brotherhood": "Fullmetal Alchemist: Brotherhood",
    "G Gundam": "Mobile Fighter G Gundam",
    "Gundam Series": "Mobile Fighter G Gundam",
    "G.I. Joe: American Hero ('89)": "G.I. Joe: American Hero (1989)",
    "G.I. Joe: Real American Hero ('83)": "G.I. Joe: Real American Hero (1983)",
    "Justice League/Unlimited": "Justice League Unlimited",
    "Mobile Suit Gundam series": "Mobile Suit Gundam",
    "New Scooby-Doo Movies": "The New Scooby-Doo Movies",
    "Scooby-Doo Movies": "The New Scooby-Doo Movies",
    "Real Advs of Jonny Quest": "Real Adventures of Jonny Quest",
    "Scooby and Scrappy": "Scooby and Scrappy-Doo",
    "Scooby-Doo! Mystery Inc.": "Scooby-Doo! Mystery Incorporated",
    "Superman: Animated Series": "Superman: The Animated Series",
    "TMNT 2K3": "Teenage Mutant Ninja Turtles (2003)",
    "Teenage Mutant Ninja Turtles 2K3": "Teenage Mutant Ninja Turtles (2003)",
    "The Batman": "The Batman (2004)",
    "Transformers '84": "Transformers (1984)",
    "Transformers ('01)": "Transformers (2001)",
    "Voltron Series": "Voltron (1984)",
}

NICK_OUTPUT     = "NickPicks.xml"
NICK_ID         = "NickPicks"
NICK_NAME       = "NickPicks"
NICK_LOGO       = "https://i.imgur.com/6is9eGi.png"
NICK_SCHED_FILE = "nickpicks_schedule.json"
NICK_DAYS       = 60                     # rolling window (perpetual weekly loop)

TSD_OUTPUT     = "ThatsSoDisney.xml"
TSD_ID         = "ThatsSoDisney"
TSD_NAME       = "That's So Disney"
TSD_LOGO       = ""                        # no logo
TSD_SCHED_FILE = "thatssodisney_schedule.json"
TSD_DAYS       = 60                     # rolling window (perpetual weekly loop)

# ── November 2026 marathon month (Nick Picks + That's So Disney) ──
# Both channels run marathons/specials all November instead of their normal week
# (the .ics calendars are the NORMAL week). Every Central date below is covered by
# two 12h filler blocks; the normal weekly grid takes over again at 12:00 AM
# Central on Dec 1. To end/extend early, change the date range.
def _month_filler(first, last, title, desc):
    d, last = datetime.strptime(first, "%Y-%m-%d"), datetime.strptime(last, "%Y-%m-%d")
    out = {}
    while d <= last:
        out[d.strftime("%Y-%m-%d")] = [[0, 720, title, desc], [720, 1440, title, desc]]
        d += timedelta(days=1)
    return out

NICK_SPECIALS = _month_filler("2026-11-01", "2026-11-30", "Non-Stop Nick",
    "No schedule, just streaks."
    "\n\n"
    "All November, NickPicks runs back-to-back marathons and specials, from SNICK-era classics "
    "and Nicktoons to TeenNick favorites and Nick at Nite late-night sitcoms, stacked episode "
    "after episode."
    "\n\n"
    "Grab the remote and settle in.")
TSD_SPECIALS = _month_filler("2026-11-01", "2026-11-30", "That's So Marathon",
    "November's one long bonanza. Back-to-back marathons of Disney Channel favorites, "
    "Zoog-era classics and Disney Afternoon toons."
    "\n\n"
    "Pick a show. Stay a while.")

RB_OUTPUT     = "RetroBlast.xml"
RB_ID         = "RetroBlast"
RB_NAME       = "RetroBlast"
RB_LOGO       = "https://i.imgur.com/m9GHMe9.png"
RB_SCHED_FILE = "retroblast_schedule.json"
RB_DAYS       = 30                      # rolling window (Fall weekly grid, US Eastern)
# One-off airings on specific (Eastern) dates, laid over the weekly grid. Rows are
# [start_min, stop_min, title, desc, sub-title(optional)]; any grid show they overlap
# is trimmed or dropped. Times are minutes from local midnight of that date.
RB_SPECIALS = {
    # Mon Nov 2, from 7 PM: Looney Tunes Cartoons mini marathon, then X-Men (2000)
    "2026-11-02": [
        [1140, 1200, "Looney Tunes Cartoons",
         "A special mini marathon of Looney Tunes Cartoons, shown in honor of Eric Bauza."],
        [1200, 1305, "X-Men (2000)",
         "Wolverine and Rogue are drawn into the war between Professor X's X-Men and Magneto's "
         "Brotherhood of Mutants. Shown in honor of Patrick Stewart."],
    ],
    # Cartoon Theater (Sat/Sun 12:10-2:15 PM)
    "2026-11-01": [[730, 855, "The Nightmare Before Christmas (1993)",
        "Jack Skellington, the Pumpkin King of Halloween Town, stumbles into Christmas Town and "
        "decides to take over the holiday."]],
    "2026-11-07": [
        [730, 775, "Class of 3000",
         "In the series premiere, music star Sunny Bridges comes home to Atlanta and becomes a "
         "music teacher at the Westley School of Performing Arts.", "Home"],
        [775, 855, "Foster's Home for Imaginary Friends",
         "In this feature-length special, Wilt suddenly leaves Foster's, and Mac and the gang set "
         "out to find him and uncover the story of his past.", "Good Wilt Hunting"],
    ],
    "2026-11-08": [
        [0, 100, "The Wizard of Oz (1939)",
         "Swept away by a tornado to the land of Oz, Dorothy follows the yellow brick road to find "
         "the Wizard who can send her home."],
        [730, 855, "Beauty and the Beast (1991)",
         "A bright young woman named Belle takes her father's place as the prisoner of a cursed "
         "Beast, and finds the kind heart hidden beneath."],
    ],
    "2026-11-14": [[730, 855, "An American Tail (1986)",
        "Fievel Mousekewitz, a young Russian mouse, is separated from his family on the voyage to "
        "America and sets out to find them in New York City."]],
    "2026-11-15": [
        [0, 100, "Wicked: Slime Tutorial with the Original Broadway Cast",
         "The original Broadway cast recording of Wicked, presented in its famous slime tutorial "
         "form, as part of an Oz-themed month of late night movies."],
        [730, 855, "The Prince of Egypt (1998)",
         "The animated story of Moses, raised as a prince of Egypt, who discovers his true "
         "heritage and leads the Hebrew people to freedom."],
    ],
    "2026-11-21": [
        [730, 790, "Tom and Jerry & the Wizard of Oz (2011)",
         "Tom and Jerry join Dorothy and Toto on the yellow brick road to the Emerald City."],
        [790, 855, "Camp Lazlo",
         "Camp Lazlo's feature-length special, starring Lazlo, Raj, Clam and the rest of Camp "
         "Kidney.", "Where's Lazlo?"],
    ],
    "2026-11-22": [
        [0, 100, "Return to Oz (1985)",
         "Dorothy returns to a ruined Oz and, with a band of new friends, must save it from the "
         "Nome King and the wicked Princess Mombi."],
        [730, 810, "Tom & Jerry: Back to Oz (2016)",
         "Tom and Jerry return to Oz with Dorothy to stop the Gnome King from taking over the land."],
        [810, 855, "Samurai Jack",
         "How the evil Aku first came to Earth, and how Jack's father defeated him, setting the "
         "stage for Jack's quest.", "The Birth of Evil"],
    ],
    "2026-11-28": [[730, 855, "Mobile Suit Gundam Wing: Endless Waltz (1998)",
        "A year after the war, the Gundam pilots are drawn back into battle when a new rebellion "
        "threatens the fragile peace between Earth and the colonies."]],
    "2026-11-29": [
        [0, 100, "The Rocky Horror Picture Show (1975)",
         "Newly engaged Brad and Janet seek help at a strange castle on a stormy night and meet "
         "the outrageous Dr. Frank-N-Furter."],
        [730, 855, "The Polar Express (2004)",
         "On Christmas Eve, a young boy boards a mysterious train bound for the North Pole."],
    ],
}

def fetch_ccn_live():
    """Read CCN's weekly lineup from the site's custom script. Returns the same
    {weekday: [[start_m, stop_m, title], ...]} shape as ccn_schedule.json, or None."""
    WD = ["Monday","Tuesday","Wednesday","Thursday","Friday","Saturday","Sunday"]
    try:
        r = requests.get(CCN_LIVE_URL, timeout=30, headers={"User-Agent": "Mozilla/5.0"})
        r.raise_for_status()
        m = re.search(r"const\s+schedule\s*=\s*(\{.*?\n\s*\});", r.text, re.S)
        if not m:
            print("  CCN live: schedule object not found in the site script - using ccn_schedule.json"); return None
        lit = re.sub(r'(^|[{,]\s*)([A-Za-z_]\w*)\s*:', lambda x: f'{x.group(1)}"{x.group(2)}":', m.group(1), flags=re.M)
        lit = re.sub(r",(\s*[}\]])", r"\1", lit)
        raw = json.loads(lit)
    except Exception as e:
        print(f"  CCN live: unavailable ({e}) - using ccn_schedule.json"); return None
    out, new_titles = {}, set()
    for d in WD:
        slots = raw.get(d) or {}
        runs = []
        for hhmm in sorted(slots):
            try:
                h, mi = map(int, hhmm.split(":"))
            except ValueError:
                continue
            title = html.unescape(str(slots[hhmm])).strip()
            if not title:
                continue
            title = CCN_RENAMES.get(title, title)
            st = h * 60 + mi
            if runs and runs[-1][2] == title and runs[-1][1] == st:
                runs[-1][1] = st + 30                  # same show continues: one longer programme
            else:
                runs.append([st, st + 30, title])
        out[d] = runs
    covered = sum(b - a for runs in out.values() for a, b, _ in runs)
    if covered < 7 * 1440 * 0.9:                       # sanity: a broken/partial read keeps the fallback
        print(f"  CCN live: only {covered // 60}h of 168h parsed - using ccn_schedule.json"); return None
    return out

def _local_to_utc(dt, zone):
    """Naive local wall time -> naive UTC, with real DST rules for any year."""
    return dt.replace(tzinfo=ZoneInfo(zone)).astimezone(timezone.utc).replace(tzinfo=None)

def _central_to_utc(dt):
    """US Central -> UTC (CDT -5 / CST -6, switches automatically every year)."""
    return _local_to_utc(dt, "America/Chicago")

def _eastern_to_utc(dt):
    """US Eastern -> UTC (EDT -4 / EST -5, switches automatically every year)."""
    return _local_to_utc(dt, "America/New_York")

def _rolling(days, zone="America/Chicago"):
    """(start, end) local dates: yesterday through +days, so the guide never runs out."""
    today = datetime.now(ZoneInfo(zone)).replace(tzinfo=None, hour=0, minute=0, second=0, microsecond=0)
    return today - timedelta(days=1), today + timedelta(days=days)

# Display title -> name to search when the schedule's title is abbreviated/non-canonical
SYN_ALIAS = {
    "Dennis the Menace ('86)": "Dennis the Menace (1986)",
    "Hellsing": "Hellsing (2001)",   # disambiguate to the 2001 series for lookup; title stays "Hellsing"
}

# ── OMDb (IMDb plots) — first choice for CCN, RetroBlast, NickPicks, TSD ─────────────────
# Free OMDb keys allow ~1,000 calls/day and the same key may be shared with other
# repos, so calls are capped per run; results (hits AND misses) live in
# desc_cache.json["omdb_syn"] and are re-checked after OMDB_TTL_DAYS.
OMDB_KEY        = os.environ.get("OMDB_API_KEY", "").strip()
OMDB_RUN_BUDGET = int(os.environ.get("OMDB_BUDGET", "150"))
OMDB_TTL_DAYS   = 60
OMDB_CHANNELS   = {"CartoonCartoonsNetwork", "RetroBlast", "NickPicks", "ThatsSoDisney"}
_omdb_left      = OMDB_RUN_BUDGET
_omdb_stats     = {"calls": 0, "hits": 0}

def _omdb_get(**params):
    global _omdb_left
    if not OMDB_KEY or _omdb_left <= 0:
        return None
    _omdb_left -= 1; _omdb_stats["calls"] += 1
    try:
        r = requests.get("https://www.omdbapi.com/", params={"apikey": OMDB_KEY, **params}, timeout=20)
        j = r.json()
        if str(j.get("Error", "")).lower().startswith("request limit"):
            _omdb_left = 0; return None
        return j
    except Exception:
        return None

def _omdb_plot(title, cache, kind="series"):
    """IMDb short plot for a show (kind='series') or film (kind='movie') via OMDb.
    Returns the plot, "" if OMDb has none, or None if not looked up this run."""
    store = cache.setdefault("omdb_syn", {})
    key = f"{kind}|{title}"
    ent = store.get(key)
    if ent and time.time() - ent.get("t", 0) < OMDB_TTL_DAYS * 86400:
        return ent.get("p", "")
    lookup = SYN_ALIAS.get(title, title)
    ym = re.search(r"\((19|20)\d\d\)", lookup)
    year = ym.group(0)[1:-1] if ym else None
    clean = re.sub(r"\s*\([^)]*\)\s*", " ", lookup).strip() or lookup   # drop (YYYY) / (Detective Conan) etc.
    q = {"t": clean, "type": kind, "plot": "short"}
    if year: q["y"] = year
    j = _omdb_get(**q)
    if j is None:
        return None                                   # out of budget / no key: try again next run
    if j.get("Response") != "True":                   # exact title missed -> search, take the best match
        s = _omdb_get(s=clean, type=kind, **({"y": year} if year else {}))
        if s is None:
            return None
        hits = s.get("Search") or []
        if hits:
            j = _omdb_get(i=hits[0]["imdbID"], plot="short") or {}
    plot = (j.get("Plot") or "").strip()
    if plot in ("N/A", ""):
        plot = ""
    store[key] = {"t": time.time(), "p": plot, "id": j.get("imdbID", "")}
    if plot: _omdb_stats["hits"] += 1
    return plot

def _omdb_episode(show, season, ep, cache):
    """IMDb episode (plot, name) via OMDb. ("", "") if unknown/out of budget (retried next run)."""
    store = cache.setdefault("omdb_syn", {})
    key = f"ep|{show}|{season}|{ep}"
    ent = store.get(key)
    if ent and time.time() - ent.get("t", 0) < OMDB_TTL_DAYS * 86400:
        return ent.get("p", ""), ent.get("n", "")
    lookup = EEL_SHOW_LOOKUP.get(show) or SYN_ALIAS.get(show, show)
    if re.search(r"\((19|20)\d\d\)", lookup):
        return "", ""        # year-disambiguated shows (DuckTales (1987)...): OMDb's title match
                             # can't take the year here, so leave them to TVmaze/TVDB
    clean = re.sub(r"\s*\([^)]*\)\s*", " ", lookup).strip() or lookup
    q = {"t": clean, "Season": season, "Episode": ep, "plot": "short"}   # no year: OMDb ignores/mis-reads it here
    j = _omdb_get(**q)
    if j is None:
        return "", ""                                 # no budget left: try again next run
    plot = (j.get("Plot") or "").strip() if j.get("Response") == "True" else ""
    name = (j.get("Title") or "").strip() if j.get("Response") == "True" else ""
    if plot == "N/A": plot = ""
    if name == "N/A": name = ""
    store[key] = {"t": time.time(), "p": plot, "n": name}
    if plot: _omdb_stats["hits"] += 1
    return plot, name

def _show_overview(title, cache, prefer_omdb=False):
    if prefer_omdb and title not in FIXED_DESC:
        p = _omdb_plot(title, cache, "series")
        if p:
            return p
    return _show_overview_db(title, cache)

def _show_overview_db(title, cache):
    """SHOW-level synopsis: TMDB -> TVmaze -> TVDB, cached. (YYYY) in title disambiguates."""
    if title in FIXED_DESC:                    # fixed override (no metadata lookup)
        return FIXED_DESC[title]
    if title in cache["show_syn"] and cache["show_syn"][title] and not _looks_foreign(cache["show_syn"][title]):
        return cache["show_syn"][title]
    lookup = SYN_ALIAS.get(title, title)
    ym = re.search(r"\((19|20)\d\d\)", lookup)
    year = ym.group(0)[1:-1] if ym else None
    clean = re.sub(r"\s*\((19|20)\d\d\)\s*", " ", lookup).strip() or lookup
    ov = ""
    if TMDB_KEY:
        params = {"query": clean}
        if year: params["first_air_date_year"] = year
        data = _tmdb_get("/search/tv", **params) or {}
        for res in (data.get("results") or [])[:3]:
            if res.get("overview") and not _looks_foreign(res["overview"]): ov = res["overview"].strip(); break
    if not ov and ENABLE_TVMAZE:
        d = _tvmaze_get("/singlesearch/shows", q=clean)
        if isinstance(d, dict) and d.get("summary"):
            ov = _TAGS.sub("", d["summary"]).strip()
    if not ov and ENABLE_TVDB:
        tid = _resolve_tvdb_id(clean, cache)
        if tid:
            d = _tvdb_get(f"/series/{tid}") or {}
            ov = (d.get("overview") or "").strip()
    cache["show_syn"][title] = ov
    return ov

def load_weekly_schedule(path):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except Exception as e:
        print(f"WARNING: cannot read {path} ({e}) - skipping"); return None

def _overlay(rows, specials):
    """Lay date-specific airings over a day's grid rows: trim/drop what they cover."""
    if not specials:
        return rows
    out = []
    for r in rows:
        segs = [(r[0], r[1])]
        for sp in specials:
            nxt = []
            for a, b in segs:
                if sp[1] <= a or sp[0] >= b:
                    nxt.append((a, b)); continue
                if a < sp[0]: nxt.append((a, sp[0]))
                if sp[1] < b: nxt.append((sp[1], b))
            segs = nxt
        for a, b in segs:
            if b - a < 5:                        # drop slivers under 5 minutes
                continue
            if a >= 1440 and any(sp[1] >= 1440 for sp in specials):
                continue                         # day replaced to midnight: no grid tail past it
            out.append([a, b] + list(r[2:]))
    return sorted(out + [list(s) for s in specials], key=lambda r: r[0])

def build_weekly(ch_id, name, logo, sched, cache, end, start=None, tz=_central_to_utc, specials=None):
    """Expand a source-local weekly grid forward over [start, end), convert to
    UTC via tz() (DST-aware), attach show-level synopses.

    Schedule rows are [start_m, stop_m, title] or [start_m, stop_m, title, desc];
    a 4th element is an inline description override (used e.g. for the Boomerang
    hour-segments, which all share the title "Boomerang")."""
    tv = ET.Element("tv", {"generator-info-name": f"{ch_id}-epg-generator"})
    ch = ET.SubElement(tv, "channel", {"id": ch_id})
    ET.SubElement(ch, "display-name").text = name
    if logo: ET.SubElement(ch, "icon", {"src": logo})
    WD = ["Monday","Tuesday","Wednesday","Thursday","Friday","Saturday","Sunday"]
    n = got = 0
    day = start or WEEKLY_START
    while day < end:
        rows = _overlay(sched.get(WD[day.weekday()], []), (specials or {}).get(day.strftime("%Y-%m-%d")))
        for row in rows:
            start_m, stop_m, title = row[0], row[1], row[2]
            inline = row[3] if len(row) > 3 else None
            subt = row[4] if len(row) > 4 else None
            st = tz(day + timedelta(minutes=start_m))
            sp = tz(day + timedelta(minutes=stop_m))
            if inline is not None:
                desc = inline
                # one-off films on CCN/RetroBlast: prefer the IMDb plot when OMDb has it
                if ch_id in OMDB_CHANNELS and re.search(r"\((19|20)\d\d\)$", title) and not subt:
                    desc = _omdb_plot(title, cache, "movie") or inline
            else:
                desc = _show_overview(title, cache, prefer_omdb=ch_id in OMDB_CHANNELS)
            p = ET.SubElement(tv, "programme", {
                "start": st.strftime("%Y%m%d%H%M%S") + " +0000",
                "stop":  sp.strftime("%Y%m%d%H%M%S") + " +0000",
                "channel": ch_id})
            ET.SubElement(p, "title", {"lang": "en"}).text = title
            if subt:
                ET.SubElement(p, "sub-title", {"lang": "en"}).text = subt
            if desc:
                ET.SubElement(p, "desc", {"lang": "en"}).text = desc; got += 1
            n += 1
        day += timedelta(days=1)
    print(f"  programmes: {n}")
    if ch_id in OMDB_CHANNELS:
        print(f"  OMDb: {'key set' if OMDB_KEY else 'no OMDB_API_KEY - using TMDB/TVmaze/TVDB'}; "
              f"calls so far this run {_omdb_stats['calls']}, new IMDb plots {_omdb_stats['hits']}")
    if TMDB_KEY: print(f"  synopses attached: {got}")
    return tv

# ── Placid (webch.nl live weekly anime block) ──────────────────────────────
# Source serves only a short window, live ~once a week (Sat). We ROLLING-MERGE
# each run into placid_state.json (committed) so captured blocks persist, prune
# old history, then fill all off-air time with 12h filler. Output Placid.xml.
# Every schedule upload gets a NEW id. The bare endpoint lists them (newest first):
#   [{"id":44,"filename":"Oct 31.xml","uploaded_at":"2026-10-30 14:45:40"}, ...]
# so we read the list each run and pull the newest few uploads.
PLACID_LIST_URL     = "https://placid.webch.nl/assets/api/schedules.php"
PLACID_URL          = PLACID_LIST_URL + "?id={id}"
PLACID_FALLBACK_ID  = 44                      # used only if the list itself can't be read
PLACID_FETCH_LATEST = 4                       # how many of the newest uploads to pull each run
PLACID_OUTPUT       = "Placid.xml"
PLACID_ID           = "Placid"
PLACID_NAME         = "Placid"
PLACID_LOGO         = "https://i.imgur.com/0PCSYdW.png"
PLACID_STATE        = "placid_state.json"   # rolling store of real programmes seen (commit it)
PLACID_KEEP_DAYS    = 21                      # retain this much past history
PLACID_HORIZON_DAYS = 14                      # extend off-air filler this far ahead of now
PLACID_FILLER_TITLE = "PLACID IS OFFLINE FOR THE WEEK"
PLACID_FILLER_DESC  = ("Only the best in anime(tion)."
                       "\n\n"
                       "Placid is live every Saturday at 5:00 PM EST.")

def _xmltv_to_utc(ts):
    """'YYYYmmddHHMMSS ±HHMM' -> naive UTC datetime."""
    parts = (ts or "").split()
    d = parts[0]; off = parts[1] if len(parts) > 1 else "+0000"
    base = datetime.strptime(d, "%Y%m%d%H%M%S")
    sign = 1 if off[0] == "+" else -1
    return base - sign * timedelta(hours=int(off[1:3]), minutes=int(off[3:5]))

def _next_grid12(dt):
    """Next 00:00 or 12:00 UTC strictly after dt (12h filler grid)."""
    b = dt.replace(hour=0, minute=0, second=0, microsecond=0)
    for h in (0, 12, 24):
        c = b + timedelta(hours=h)
        if c > dt:
            return c
    return dt + timedelta(hours=12)

def fetch_placid_uploads():
    """Newest Placid schedule uploads as a list of XML roots, OLDEST first (so a newer
    upload overrides an older one where they overlap)."""
    ids = []
    try:
        r = requests.get(PLACID_LIST_URL, timeout=30, headers={"User-Agent": "Mozilla/5.0"})
        r.raise_for_status()
        rows = [x for x in r.json() if isinstance(x, dict) and str(x.get("id", "")).isdigit()]
        rows.sort(key=lambda x: (x.get("uploaded_at") or "", int(x["id"])))
        ids = [int(x["id"]) for x in rows][-PLACID_FETCH_LATEST:]
        print(f"  Placid uploads listed: {len(rows)}; using ids {ids} "
              f"(newest: {rows[-1].get('filename')} uploaded {rows[-1].get('uploaded_at')})" if rows else "  Placid: empty upload list")
    except Exception as e:
        print(f"WARNING: Placid upload list unreadable ({e}) - falling back to id {PLACID_FALLBACK_ID}")
    if not ids:
        ids = [PLACID_FALLBACK_ID]
    roots = []
    for i in ids:
        root = fetch_xml_safe(PLACID_URL.format(id=i), f"Placid id {i}")
        if root.findall("programme"):
            roots.append(root)
    return roots

def build_placid(src_roots, state_path=PLACID_STATE, now=None):
    now = now or datetime.utcnow()
    try:
        with open(state_path, encoding="utf-8") as f:
            state = json.load(f)
    except Exception:
        state = {}
    added = 0
    if not isinstance(src_roots, (list, tuple)):
        src_roots = [src_roots]
    for src_root in src_roots:                    # oldest upload first
        upl = [p for p in src_root.findall("programme") if p.get("start") and p.get("stop")]
        if not upl:
            continue
        # a newer upload REPLACES whatever we had inside its time span (handles reshuffles)
        a = min(_xmltv_to_utc(p.get("start")) for p in upl)
        b = max(_xmltv_to_utc(p.get("stop")) for p in upl)
        state = {k: v for k, v in state.items() if not (a <= _xmltv_to_utc(k) < b)}
        for prog in upl:
            np = ET.fromstring(ET.tostring(prog)); np.set("channel", PLACID_ID)
            _strip_local_images(np)
            key = np.get("start")
            if key not in state:
                added += 1
            state[key] = ET.tostring(np, encoding="unicode")        # add or refresh
    cutoff = now - timedelta(days=PLACID_KEEP_DAYS)
    state = {k: v for k, v in state.items() if _xmltv_to_utc(k) >= cutoff}
    with open(state_path, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=0, sort_keys=True)

    tv = ET.Element("tv", {"generator-info-name": "placid-epg-generator"})
    ch = ET.SubElement(tv, "channel", {"id": PLACID_ID})
    ET.SubElement(ch, "display-name").text = PLACID_NAME
    ET.SubElement(ch, "icon", {"src": PLACID_LOGO})

    reals = []
    for xmlstr in state.values():
        p = ET.fromstring(xmlstr)
        reals.append((_xmltv_to_utc(p.get("start")), _xmltv_to_utc(p.get("stop")), p))
    reals.sort(key=lambda r: r[0])

    span_start = min([r[0] for r in reals] + [now]) if reals else now
    span_end   = max([r[1] for r in reals] + [now + timedelta(days=PLACID_HORIZON_DAYS)])

    def add_filler(a, b):
        t = a
        while t < b:
            end = min(_next_grid12(t), b)
            fp = ET.SubElement(tv, "programme", {
                "start": t.strftime("%Y%m%d%H%M%S") + " +0000",
                "stop":  end.strftime("%Y%m%d%H%M%S") + " +0000",
                "channel": PLACID_ID})
            ET.SubElement(fp, "title", {"lang": "en"}).text = PLACID_FILLER_TITLE
            ET.SubElement(fp, "desc",  {"lang": "en"}).text = PLACID_FILLER_DESC
            t = end

    cursor = span_start
    for a, b, p in reals:
        if a > cursor:
            add_filler(cursor, a)
        tv.append(p)
        if b > cursor:
            cursor = b
    if cursor < span_end:
        add_filler(cursor, span_end)
    print(f"  Placid: {len(reals)} real programmes (+{added} new this run), filler to now+{PLACID_HORIZON_DAYS}d")
    return tv

# ── 40 Media Group (ENT + Totalmusic FAST channels) ─────────────────────────
# Each channel exposes a JSON guide at api.40mediagroup.com. Times are already
# ISO-8601 in UTC (…+00:00) so no tz conversion is needed (verified against the
# live on-air anchor). Titles/sub-titles/descriptions/categories are the feed's
# own Spanish-localized text, copied as-is. tvg-id == the JSON url slug.
# Rebuilt once per UTC day: the <tv date="YYYYMMDD"> stamp gates same-day reruns
# (the Whiplash workflow fires several times a day; this output only changes once).
MEDIA40_OUTPUT   = "40media.xml"
MEDIA40_URL      = "https://api.40mediagroup.com/xmltv/programacion/{slug}/guia.json"
MEDIA40_HEADERS  = {**BROWSER_HEADERS, "Accept": "application/json, text/plain, */*"}
# (tvg-id / url-slug, display-name, logo)
MEDIA40_CHANNELS = [
    ("entchannel",     "ENT Channel",      "https://i.imgur.com/5w7jlcr.png"),
    ("entclassic",     "ENT Classic",      "https://i.imgur.com/42wUAun.png"),
    ("entcomedy",      "ENT Comedy",       "https://i.imgur.com/22yAycO.png"),
    ("entdrama",       "ENT Drama",        "https://i.imgur.com/ARLD4hQ.png"),
    ("entextreme",     "ENT Extreme",      "https://i.imgur.com/AZwQU5n.png"),
    ("entfamily",      "ENT Family",       "https://i.imgur.com/ez5UE1a.png"),
    ("entlife",        "ENT Life",         "https://i.imgur.com/V6hdLT0.png"),
    ("entmovies",      "ENT Movies",       "https://i.imgur.com/wVcolSX.png"),
    ("totalmusic",     "Totalmusic",       "https://i.imgur.com/S9i0Vi4.png"),
    ("totalmusic-80s", "Totalmusic 80s",   "https://i.imgur.com/uG229hI.png"),
    ("totalmusic-00s", "Totalmusic 2000s", "https://i.imgur.com/JResjBY.png"),
]

def _iso_to_xmltv(s):
    """ISO-8601 (feed is already UTC, +00:00) -> 'YYYYmmddHHMMSS +0000'."""
    dt = datetime.fromisoformat(s)
    dt = dt.astimezone(timezone.utc) if dt.tzinfo else dt
    return dt.strftime("%Y%m%d%H%M%S") + " +0000"

def build_40media(now=None):
    """Scrape the 11 40 Media Group JSON guides into one XMLTV tree. Returns the
    tree, or None to leave the committed 40media.xml untouched (already built today,
    or every feed failed)."""
    now = now or datetime.utcnow()
    today = now.strftime("%Y%m%d")
    try:                                   # once-a-day gate
        if ET.parse(MEDIA40_OUTPUT).getroot().get("date") == today:
            print(f"  40media: already built today ({today}) - skipping")
            return None
    except Exception:
        pass

    tv = ET.Element("tv", {"generator-info-name": "40media-epg-generator", "date": today})
    for slug, name, logo in MEDIA40_CHANNELS:      # declare every channel up front
        ch = ET.SubElement(tv, "channel", {"id": slug})
        ET.SubElement(ch, "display-name").text = name
        if logo:
            ET.SubElement(ch, "icon", {"src": logo})

    ok = total = 0
    for slug, name, logo in MEDIA40_CHANNELS:
        try:
            r = requests.get(MEDIA40_URL.format(slug=slug), headers=MEDIA40_HEADERS, timeout=30)
            r.raise_for_status()
            progs = (r.json() or {}).get("programmes") or []
        except Exception as e:
            print(f"  40media {slug}: fetch failed ({e}) - channel left empty this run")
            continue
        n = 0
        for pr in progs:
            try:
                st, sp = _iso_to_xmltv(pr["start"]), _iso_to_xmltv(pr["stop"])
            except Exception:
                continue
            p = ET.SubElement(tv, "programme", {"start": st, "stop": sp, "channel": slug})
            ET.SubElement(p, "title", {"lang": "es"}).text = (pr.get("title") or "").strip() or name
            for src, tag in (("subtitle", "sub-title"), ("desc", "desc"), ("category", "category")):
                val = (pr.get(src) or "").strip()
                if val:
                    ET.SubElement(p, tag, {"lang": "es"}).text = val
            icon = (pr.get("icon") or "").strip()
            if icon:
                ET.SubElement(p, "icon", {"src": icon})
            n += 1
        ok += 1; total += n
        print(f"  40media {slug}: {n} programmes")
    if ok == 0:
        print("  40media: ALL feeds failed - keeping existing 40media.xml unchanged")
        return None
    print(f"  40media: {ok}/{len(MEDIA40_CHANNELS)} channels, {total} programmes")
    return tv

# ── Locomotion (fan-revived Latin American anime channel) ────────────────────
# Source: the channel's own XMLTV guide. It went stale in Jan 2026 (3 identical
# days), but the channel still plays that same 24h schedule every day - verified
# Oct 25 2026 on air (Duckman, then South Park on the half hour). Its wall-clock
# times are re-read at LOCO_UTC_OFFSET_H: the stream ran at UTC-5 on Oct 25, then
# moved to UTC-4 (= the file's own -0400) by Nov 2 2026 - verified on air (Los
# Cazadores de Duendes after Evangelion). If the feed ever covers "now" again, its
# real dates are used (same offset); otherwise its latest full day is looped forward.
LOCO_URL          = "http://epg.locomotiontv.com/guia.xml"
LOCO_OUTPUT       = "Locomotion.xml"
LOCO_ID           = "Locomotion"
LOCO_NAME         = "Locomotion"
LOCO_LOGO         = "https://i.imgur.com/g5psxlY.png"
LOCO_SRC_CHANNEL  = "Locomotion"
LOCO_UTC_OFFSET_H = -4        # channel's real clock (UTC-4 since Nov 2026); change if it drifts an hour
LOCO_DAYS         = 14        # loop this many days ahead

def _loco_wallclock(ts):
    """'YYYYmmddHHMMSS ±HHMM' -> naive wall-clock datetime (offset ignored on purpose)."""
    return datetime.strptime((ts or "").split()[0], "%Y%m%d%H%M%S")

def build_locomotion(src_root, now=None):
    now = now or datetime.utcnow()
    progs = [p for p in src_root.findall("programme") if p.get("channel") == LOCO_SRC_CHANNEL]
    if not progs:
        return None                                   # fetch failed: keep last file
    off = timedelta(hours=LOCO_UTC_OFFSET_H)
    def utc(wall): return wall - off                  # wall-clock at UTC-5 -> UTC
    items = []
    for p in progs:
        try:
            a, b = _loco_wallclock(p.get("start")), _loco_wallclock(p.get("stop"))
        except ValueError:
            continue
        if b > a:
            items.append((a, b, p))
    items.sort(key=lambda x: x[0])
    tv = ET.Element("tv", {"generator-info-name": "locomotion-epg-generator"})
    ch = ET.SubElement(tv, "channel", {"id": LOCO_ID})
    ET.SubElement(ch, "display-name").text = LOCO_NAME
    ET.SubElement(ch, "icon", {"src": LOCO_LOGO})

    def emit(start_utc, stop_utc, p):
        np_ = ET.SubElement(tv, "programme", {
            "start": start_utc.strftime("%Y%m%d%H%M%S") + " +0000",
            "stop":  stop_utc.strftime("%Y%m%d%H%M%S") + " +0000",
            "channel": LOCO_ID})
        for child in p:
            if child.tag in ("title", "sub-title", "desc", "date", "category", "icon", "episode-num"):
                np_.append(ET.fromstring(ET.tostring(child)))

    if items and utc(items[-1][1]) > now + timedelta(hours=24):
        for a, b, p in items:                          # feed is current: use its dates
            emit(utc(a), utc(b), p)
        print(f"  Locomotion: live guide is current - {len(items)} programmes")
        return tv

    # stale: take the latest complete day and repeat it daily
    last_day = items[-1][0].date()
    day = [(a, b, p) for a, b, p in items if a.date() == last_day]
    if sum((b - a).total_seconds() for a, b, _ in day) < 20 * 3600:   # partial last day
        prev = last_day - timedelta(days=1)
        day = [(a, b, p) for a, b, p in items if a.date() == prev] or day
    base = day[0][0].replace(hour=0, minute=0, second=0)
    template = [(a - base, b - base, p) for a, b, p in day]
    first = (now + off).replace(hour=0, minute=0, second=0, microsecond=0) - timedelta(days=1)
    n = 0
    for d in range(LOCO_DAYS + 1):
        day0 = first + timedelta(days=d)
        for sa, sb, p in template:
            emit(utc(day0 + sa), utc(day0 + sb), p); n += 1
    print(f"  Locomotion: guide is stale (last day {last_day}) - looped its "
          f"{len(template)}-slot day for {LOCO_DAYS + 1} days at UTC{LOCO_UTC_OFFSET_H:+d} ({n} programmes)")
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

EPG_OUTPUT = "Whiplash.xml"          # renamed from epg.xml (same tvg-ids)
M3U_OUTPUT = "playlist.m3u"
EPG_RAW_URL = "https://raw.githubusercontent.com/s-digweed/Whiplash/main/Whiplash.xml"

# ── Webchnl dummies (webchnldummies.xml) ──────────────────────────────────────
# Guide for the Webchnl playlist's dummy channels: the "##### GROUP #####" separators
# that head each group in TiviMate (guide row just repeats the name) plus simple
# filler channels like Aurora. tvg-id here = tvg-id in webchnl.m3u.
DUMMIES_OUTPUT = "webchnldummies.xml"
SEPARATORS = [
    ("SEP.Webchnl",   "##### WEBCHNL #####",       "https://i.imgur.com/SGcDJuQ.png"),
    ("SEP.Vueue",     "##### VUEUE #####",         "https://i.imgur.com/EPyPPzh.png"),
    ("SEP.RetroTV",   "##### RETRO TV #####",      "https://i.imgur.com/LT3nBqW.png"),
    ("SEP.MistLive",  "##### MIST LIVE #####",     "https://i.imgur.com/vZhDOlD.png"),
    ("SEP.40Media",   "##### 40MEDIA GROUP #####", "https://i.imgur.com/Q9lOrSk.png"),
    ("SEP.Others",    "##### OTHERS #######",      "https://i.imgur.com/6UZEDRL.png"),
    ("SEP.Kift",      "##### KIFT #####",          "https://i.imgur.com/TZQU11E.png"),
    ("SEP.USWebchnl", "##### US - WEBCHNL #####",  "https://i.imgur.com/SGcDJuQ.png",
     "##### US - WEBCHNL #####"),               # optional 4th field = description
]
# (tvg-id, display name, logo, title, description, block hours)
DUMMY_CHANNELS = [
    ("Aurora", "Aurora", "https://i.imgur.com/KHHOX8e.png", "Aurora",
     "Aurora is a family channel broadcasting cartoons, anime and live-action films every weekend.", 12),
    ("flashBAK", "flashBAK", "https://i.imgur.com/AWzw5cX.png", "flashBAK",
     "Take a break from the modern world. Come say hello again to the shows, movies, and songs that defined your childhood.", 12),
    ("TLPlus", "TL+", "https://i.imgur.com/TbL9E10.png", "TL+",
     "Somos un canal de Televisión online de origen salvadoreño con programación de contenido anime para toda América Latina.", 12),
    ("Magical", "Magical", "https://i.imgur.com/NhU22Zs.png", "Magical",
     "Magical celebrates several anime genres from magical girl to idol culture.", 12),
    ("OptiradioTV", "Optiradio TV", "https://i.imgur.com/7BSz9wO.png", "Optiradio TV",
     "Optiradio TV", 12),
    ("DIJIT", "DIJIT", "https://i.imgur.com/7h0QRo9.png", "DIJIT / Joy.Rebel",
     "Accept no imitation.", 12),
    ("Dotwave", "Dotwave", "https://i.imgur.com/GpmmAxf.png", "Dotwave",
     "Canada's spot for comedy. From sitcoms like Fresh Prince to reality comedies like Kenny vs. Spenny.\n\nWe're comedy on the dot.", 12),
    ("NICAPlus", "NICA+", "https://i.imgur.com/05LqN3Q.png", "NICA+",
     "El primer canal online en Nicaragua trayendo la mejor programación Geek hacia los chavalos nicaragüenses con un gran orgullo pinolero.", 12),
    ("JNIME", "JNIME", "https://i.imgur.com/kVC9ASD.png", "JNIME",
     "it feels right at home.", 12),
    ("WYLP", "WYLP", "https://i.imgur.com/yzydOWR.png", "WYLP 5",
     "WYLP, also known as Channel 5, is an independent low-power analog television station in York, Pennsylvania.\n\nThe station primarily broadcasts sitcoms from the 1980s and 1990s, cartoons and movies, in the structure of a mid-to-late 90s independent TV station.", 12),
    ("OTVN", "OTVN", "https://i.imgur.com/Tx28h4X.png", "OTVN",
     "When the other toon channels weren't enough for some reason, you find yourself buried so deep in video tapes that you'd have to get someone to do some shoveling to get you out.", 12),
    ("CrossRift", "CrossRift", "https://i.imgur.com/bLuLNHs.png", "CROSSRIFT IS OFFLINE. PLEASE STAND BY.",
     "CrossRift is an animation channel all about serving obscure cartoons by day and obscure anime by night. "
     "Comes with morning video game music through V.G.R (Video Game Radio) and nightly live action programming "
     "through Terra.\n\nSurfing through the Obscure.", 12),
    ("TelePosadas", "Tele Posadas", "https://i.imgur.com/XJD65oi.png", "Tele Posadas",
     "Entretenimiento y películas en vivo desde Posadas, Misiones.", 12),
    ("ObjectCentral", "Object Central", "https://i.imgur.com/Sm3bF3R.png", "Object Central",
     "A TV Channel for the osc!", 12),
    ("Telepix", "Telepix", "https://i.imgur.com/6CXVNAC.png", "Telepix",
     "Offering popular movies and shows you won't find anywhere else, Telepix is your Movie Hub.", 12),
    ("Collective", "Collective", "https://i.imgur.com/pMdLPNI.png", "Collective",
     "Tune in every day for the best dance tunes and chart topping hits.", 12),
    ("HubNetwork", "Hub Network", "https://i.imgur.com/HH5Dj6q.png", "Hub Network",
     "Hub Network", 12),
    ("NFKTV", "NFKTV", "https://i.imgur.com/GFMGxJ4.png", "NFKTV: Not your childhood network",
     "NFKTV (not for kids) is a mature channel that focuses on adult animation.", 12),
    ("Zip", ">zip.", "https://i.imgur.com/p43LXLK.png", ">zip.",
     ">zip. is an entertainment television station launched in 2022.", 12),
    ("Ultra", "ULTRA!", "https://i.imgur.com/KRPDEKf.png", "ULTRA!",
     "ITS ALL HERE FOR YA!", 12),
    ("Vortex2", "VORTEX2", "https://i.imgur.com/g1zjy2R.png", "VORTEX2",
     "VORTEX2", 12),
    ("AfterSwim", "[after swim]", "https://i.imgur.com/eMyNV35.png", "[after swim]",
     "[after swim]", 12),
    ("NNRetro", "Nicktoons Network Retro", "https://i.imgur.com/rFfQmKL.png", "Nicktoons Network Retro",
     "Nicktoons Network Retro", 12),
    ("WhiplashFM", "Whiplash FM", "https://i.imgur.com/aBjYjZz.png", "Whiplash FM",
     "Nothing but beats.", 12),
    ("SwimRewind", "Swim Rewind", "https://i.imgur.com/WwOUcmM.png", "Swim Rewind",
     "THIS STREAM IS OFFLINE.", 12),
    ("CNExtras", "CN Extras", "https://i.imgur.com/sCOrQv4.png", "CN Extras",
     "CNEX is a webchannel based on the CHECK it 3.0 era and Toonami's 2014 era. All your favorite programming from 2013-2015, brought in an era-accurate package. With custom GIFs and Promotional Material, we make sure to bring back your nostalgia!", 12),
    ("ThrowbackTube", "ThrowbackTube", "https://i.imgur.com/DId341p.png", "ThrowbackTube",
     "ThrowbackTube", 12),
    ("RetroNick", "RetroNick", "https://i.imgur.com/Tx9YMlJ.png", "RetroNick",
     "RetroNick", 12),
    ("EnerGeek", "EnerGeek", "https://i.imgur.com/clbbkA3.png", "EnerGeek",
     "El canal insignia de la familia EnerGeek te transporta a través de un viaje nostálgico con una cuidadosa selección de series y películas icónicas de las décadas de los 80, 90 y 2000. Además, ofrece un contenido original producido por su talentoso equipo, garantizando una experiencia única. Prepárate para sumergirte en una emocionante programación que te hará revivir momentos inolvidables y despertarán una nostalgia inigualable.", 12),
    ("EnerGeekRadio", "EnerGeek Radio", "https://i.imgur.com/2PQ1wFT.png", "EnerGeek Radio",
     "Canal parte de la familia EnerGeek, donde podrás explorar un poco de la cultura chilena mientras te deleitas con las mejores melodías de K-Pop, J-Pop y J-Rock. Además, no te pierdas la oportunidad de disfrutar de la producción de algunos de nuestros programas originales. ¡Una experiencia única que combina lo mejor de la música y la diversidad cultural!", 12),
    ("EnerGeekFan", "EnerGeek Fan", "https://i.imgur.com/spdqBo8.png", "EnerGeek Fan",
     "Este canal, parte de la familia EnerGeek, ofrece una programación diversa las 24 horas del día. Desde emocionantes caricaturas hasta cautivadoras series de animación japonesa, pasando por vibrantes series live-action y divertidas sitcoms, es el destino perfecto para todos los amantes del entretenimiento.", 12),
]
DUMMY_DAYS = 14

def build_dummies():
    tv = ET.Element("tv", {"generator-info-name": "webchnl-dummies"})
    day0 = datetime.now(timezone.utc).replace(hour=0, minute=0, second=0, microsecond=0) - timedelta(days=1)
    rows = [(sep[0], sep[1], sep[2], sep[1], (sep[3] if len(sep) > 3 else None), 24)
            for sep in SEPARATORS] + DUMMY_CHANNELS
    for cid, name, logo, *_ in rows:
        ch = ET.SubElement(tv, "channel", {"id": cid})
        ET.SubElement(ch, "display-name").text = name
        if logo:
            ET.SubElement(ch, "icon", {"src": logo})
    for cid, _, _, title, desc, hours in rows:
        t, end = day0, day0 + timedelta(days=DUMMY_DAYS + 1)
        while t < end:
            pr = ET.SubElement(tv, "programme", {"start": t.strftime("%Y%m%d%H%M%S +0000"),
                                                 "stop": (t + timedelta(hours=hours)).strftime("%Y%m%d%H%M%S +0000"),
                                                 "channel": cid})
            ET.SubElement(pr, "title", {"lang": "en"}).text = title
            if desc:
                ET.SubElement(pr, "desc", {"lang": "en"}).text = desc
            t += timedelta(hours=hours)
    return tv

def build_all(wl_root, eel_root, cache):
    tv = ET.Element("tv", {"generator-info-name": "whiplash-eel-epg-generator"})
    add_channels(tv, WL_CHANNEL_MAP, WL_LOGOS)
    add_channels(tv, EEL_CHANNEL_MAP, EEL_LOGOS)
    print("Whiplash:"); copy_whiplash(tv, wl_root)
    print("Eel:");      build_eel(tv, eel_root, cache)
    return tv


def _scrub(root):
    """Safety net before any guide is written: drop U+FFFD (garbled characters crash IPTVBoss)."""
    for el in root.iter():
        if el.text and "\ufffd" in el.text: el.text = el.text.replace("\ufffd", "")
        if el.tail and "\ufffd" in el.tail: el.tail = el.tail.replace("\ufffd", "")
        for k, v in list(el.attrib.items()):
            if "\ufffd" in v: el.set(k, v.replace("\ufffd", ""))
    return root

def main():
    cache = load_desc_cache()
    if not TMDB_KEY:
        print("NOTE: TMDB_API_KEY not set - descriptions skipped this run.")
    print(f"Fetching {WL_URL} ...");  wl_root  = fetch_xml_safe(WL_URL, "Whiplash")
    print(f"Fetching {EEL_URL} ..."); eel_root = fetch_xml_safe(EEL_URL, "Eel")
    tv = build_all(wl_root, eel_root, cache)
    indent(tv)
    ET.ElementTree(_scrub(tv)).write(EPG_OUTPUT, encoding="UTF-8", xml_declaration=True)
    with open(M3U_OUTPUT, "w", encoding="utf-8") as f: f.write(build_m3u())
    print(f"Wrote {EPG_OUTPUT} and {M3U_OUTPUT}")
    print(f"Channels: {len(tv.findall('channel'))}, programmes: {len(tv.findall('programme'))}")

    print(f"Fetching {MIST_URL} ...")
    mist_root = fetch_mist(MIST_URL)
    if mist_root.findall("channel") or mist_root.findall("programme"):
        print("MistLive:"); mtv = build_mist(mist_root, cache)
        indent(mtv)
        ET.ElementTree(_scrub(mtv)).write(MIST_OUTPUT, encoding="UTF-8", xml_declaration=True)
        print(f"Wrote {MIST_OUTPUT}")
        print(f"Channels: {len(mtv.findall('channel'))}, programmes: {len(mtv.findall('programme'))}")
    else:
        print(f"MistLive feed empty/unavailable - keeping existing {MIST_OUTPUT} unchanged")

    ccn_s, ccn_e   = _rolling(CCN_DAYS)
    nick_s, nick_e = _rolling(NICK_DAYS)
    tsd_s, tsd_e   = _rolling(TSD_DAYS)
    rb_s, rb_e     = _rolling(RB_DAYS, "America/New_York")
    # CCN: prefer the live site lineup; keep ccn_schedule.json in step as the fallback
    ccn_live = fetch_ccn_live()
    if ccn_live:
        try:
            old = load_weekly_schedule(CCN_SCHED_FILE) or {}
        except Exception:
            old = {}
        changed = sum(1 for d in ccn_live for row in ccn_live[d] if row not in (old.get(d) or []))
        if changed:
            with open(CCN_SCHED_FILE, "w", encoding="utf-8") as f:
                json.dump(ccn_live, f, ensure_ascii=False, indent=1)
            print(f"  CCN live: lineup CHANGED on the site ({changed} programme slots) - ccn_schedule.json updated")
        else:
            print("  CCN live: lineup read from the site, no change")
        unmapped = sorted({t for d in ccn_live for _, _, t in ccn_live[d]} - {t for d in old for _, _, t in old[d]})
        if unmapped:
            print("  CCN live: new titles (add to CCN_RENAMES if they need a cleaner name): " + "; ".join(unmapped))
    for out, cid, nm, logo, sfile, end, start, tz in (
        (CCN_OUTPUT,  CCN_ID,  CCN_NAME,  CCN_LOGO,  CCN_SCHED_FILE,  ccn_e,  ccn_s,  _central_to_utc),
        (NICK_OUTPUT, NICK_ID, NICK_NAME, NICK_LOGO, NICK_SCHED_FILE, nick_e, nick_s, _central_to_utc),
        (TSD_OUTPUT,  TSD_ID,  TSD_NAME,  TSD_LOGO,  TSD_SCHED_FILE,  tsd_e,  tsd_s,  _central_to_utc),
        (RB_OUTPUT,   RB_ID,   RB_NAME,   RB_LOGO,   RB_SCHED_FILE,   rb_e,   rb_s,   _eastern_to_utc)):
        sched = load_weekly_schedule(sfile)
        if not sched:
            continue
        print(f"{nm}:"); wtv = build_weekly(cid, nm, logo, sched, cache, end, start, tz,
                                            specials={RB_ID: RB_SPECIALS, NICK_ID: NICK_SPECIALS,
                                                      TSD_ID: TSD_SPECIALS}.get(cid))
        indent(wtv)
        ET.ElementTree(_scrub(wtv)).write(out, encoding="UTF-8", xml_declaration=True)
        print(f"Wrote {out}")
        print(f"Channels: {len(wtv.findall('channel'))}, programmes: {len(wtv.findall('programme'))}")

    print(f"Fetching Placid uploads from {PLACID_LIST_URL} ...")
    placid_src = fetch_placid_uploads()
    print("Placid:"); ptv = build_placid(placid_src)
    indent(ptv)
    ET.ElementTree(_scrub(ptv)).write(PLACID_OUTPUT, encoding="UTF-8", xml_declaration=True)
    print(f"Wrote {PLACID_OUTPUT}")
    print(f"Channels: {len(ptv.findall('channel'))}, programmes: {len(ptv.findall('programme'))}")

    print("40 Media Group:")
    mtv40 = build_40media()
    if mtv40 is not None:
        indent(mtv40)
        ET.ElementTree(_scrub(mtv40)).write(MEDIA40_OUTPUT, encoding="UTF-8", xml_declaration=True)
        print(f"Wrote {MEDIA40_OUTPUT}")
        print(f"Channels: {len(mtv40.findall('channel'))}, programmes: {len(mtv40.findall('programme'))}")

    print(f"Fetching {LOCO_URL} ...")
    loco_src = fetch_xml_safe(LOCO_URL, "Locomotion", headers=BROWSER_HEADERS)
    print("Locomotion:"); ltv = build_locomotion(loco_src)
    if ltv is not None:
        indent(ltv)
        ET.ElementTree(_scrub(ltv)).write(LOCO_OUTPUT, encoding="UTF-8", xml_declaration=True)
        print(f"Wrote {LOCO_OUTPUT} ({len(ltv.findall('programme'))} programmes)")
    else:
        print(f"  Locomotion feed empty/unavailable - keeping existing {LOCO_OUTPUT}")

    print("Webchnl dummies:")
    dtv = build_dummies()
    indent(dtv)
    ET.ElementTree(_scrub(dtv)).write(DUMMIES_OUTPUT, encoding="UTF-8", xml_declaration=True)
    print(f"Wrote {DUMMIES_OUTPUT} ({len(dtv.findall('channel'))} channels, {len(dtv.findall('programme'))} programmes)")

    save_desc_cache(cache)

if __name__ == "__main__":
    main()
