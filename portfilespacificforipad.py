#!/usr/bin/env python3
"""
Cinema - a tiny personal streaming server (Netflix-style UI, HLS / direct play)

Run:      python movie_server.py
Open:     http://localhost:8000   (or the iPad / phone URL printed at start-up)

What it does
  * Direct play   - MP4/M4V/MOV/WebM with browser-friendly codecs are served as-is
                    (zero CPU, instant seeking).
  * Fast remux    - H.264 sources are re-packaged to HLS without re-encoding.
  * Transcode     - everything else is encoded to H.264/AAC (GPU encoder is used
                    automatically when one is available) and capped at 1080p.
  * Jobs are throttled when the buffer is full, stopped when you leave, and their
    temporary files are deleted, so nothing keeps eating CPU or disk.
"""

import atexit
import collections
import hashlib
import json
import os
import re
import shutil
import socket
import subprocess
import sys
import threading
import time
import urllib.request
import uuid
from concurrent.futures import ThreadPoolExecutor
from html import escape
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, quote, unquote, urlparse

try:  # Windows consoles with legacy code pages must never crash on a print()
    sys.stdout.reconfigure(errors="replace")
except Exception:
    pass


# ============================================================
# CONFIGURATION
# ============================================================

APP_NAME = "Cinema"

MOVIE_DIR = Path(os.environ.get("MOVIE_DIR", r"I:\Movies\Movies"))
PORT = int(os.environ.get("PORT", "8000"))

SEGMENT_TIME = 4                # seconds per HLS segment (smaller = faster start)
BUFFER_AHEAD_SECONDS = 180      # pause ffmpeg when it is this far ahead of the player
IDLE_TIMEOUT = 600              # stop a stream nobody has touched for this long (s)
MAX_HEIGHT = 1080               # transcodes are scaled down to this height
COPY_MAX_BITRATE = 20_000_000   # H.264 above this is transcoded, not remuxed (bit/s)
USE_GPU_ENCODER = True          # try NVENC / QuickSync / AMF before libx264
PROBE_WORKERS = 4               # parallel ffprobe processes while indexing

HLS_JS_VERSION = "1.5.20"
HLS_JS_CDN = f"https://cdn.jsdelivr.net/npm/hls.js@{HLS_JS_VERSION}/dist/hls.min.js"

VIDEO_FORMATS = {
    ".mkv", ".mp4", ".m4v", ".avi", ".mov",
    ".wmv", ".flv", ".ts", ".m2ts", ".webm", ".ogv",
}
IGNORED_DIRS = {".hls", ".converted", "ffmpeg", ".git", "$recycle.bin", "system volume information"}

MIME = {
    ".mkv": "video/x-matroska", ".mp4": "video/mp4", ".m4v": "video/mp4",
    ".mov": "video/quicktime", ".webm": "video/webm", ".avi": "video/x-msvideo",
    ".wmv": "video/x-ms-wmv", ".flv": "video/x-flv", ".ts": "video/mp2t",
    ".m2ts": "video/mp2t", ".ogv": "video/ogg",
}

ROOT = MOVIE_DIR.resolve()
HLS_DIR = ROOT / ".hls"
THUMBS_DIR = HLS_DIR / "thumbnails"
CACHE_FILE = HLS_DIR / "metadata_cache.json"
PROGRESS_FILE = HLS_DIR / "progress.json"
HLS_JS_FILE = HLS_DIR / f"hls-{HLS_JS_VERSION}.min.js"

EXE = ".exe" if os.name == "nt" else ""
NO_WINDOW = 0x08000000 if os.name == "nt" else 0


def log(msg):
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)


# ============================================================
# FFMPEG / FFPROBE DISCOVERY
# ============================================================

def find_binary(name):
    exe_dir = Path(sys.executable).parent
    meipass = Path(getattr(sys, "_MEIPASS", exe_dir))
    local = [
        meipass / "ffmpeg" / "bin" / f"{name}{EXE}",
        meipass / f"{name}{EXE}",
        exe_dir / "ffmpeg" / "bin" / f"{name}{EXE}",
        exe_dir / f"{name}{EXE}",
        ROOT / "ffmpeg" / "bin" / f"{name}{EXE}",
        ROOT / f"{name}{EXE}",
        ROOT / "bin" / f"{name}{EXE}",
        ROOT.parent / "ffmpeg" / "bin" / f"{name}{EXE}",
        Path(r"I:\Movies\ffmpeg\bin") / f"{name}{EXE}",
    ]
    for p in local:
        if p.exists():
            return str(p)
    found = shutil.which(name)
    if found:
        return found
    if os.name == "nt":
        for p in (
            Path(rf"C:\ffmpeg\bin\{name}.exe"),
            Path(rf"C:\Program Files\ffmpeg\bin\{name}.exe"),
            Path(rf"C:\Program Files (x86)\ffmpeg\bin\{name}.exe"),
        ):
            if p.exists():
                return str(p)
    return None


FFMPEG = find_binary("ffmpeg")
FFPROBE = find_binary("ffprobe")
if FFMPEG and not FFPROBE:
    sibling = Path(FFMPEG).with_name(f"ffprobe{EXE}")
    if sibling.exists():
        FFPROBE = str(sibling)

if not ROOT.is_dir():
    print(f"\nERROR: movie folder not found: {ROOT}\n"
          f"Edit MOVIE_DIR at the top of this file (or set the MOVIE_DIR environment variable).\n")
    input("Press ENTER to exit...")
    sys.exit(1)

if not FFMPEG:
    print("\n" + "=" * 60)
    print("ERROR: FFMPEG NOT FOUND")
    print("=" * 60)
    print(rf"Expected at: {ROOT}\ffmpeg\bin\ffmpeg.exe  (or anywhere on PATH)")
    print("Put ffmpeg.exe and ffprobe.exe in that folder and start again.\n")
    input("Press ENTER to exit...")
    sys.exit(1)


def run(cmd, timeout):
    return subprocess.run(
        cmd, capture_output=True, text=True, encoding="utf-8", errors="replace",
        timeout=timeout, stdin=subprocess.DEVNULL, creationflags=NO_WINDOW,
    )


# ============================================================
# ENCODER SELECTION (GPU if it really works, else libx264)
# ============================================================

SOFTWARE_ENCODER = (
    "libx264",
    ["-c:v", "libx264", "-preset", "ultrafast", "-crf", "23",
     "-maxrate", "12M", "-bufsize", "24M", "-sc_threshold", "0"],
)

GPU_ENCODERS = [
    ("h264_nvenc", ["-c:v", "h264_nvenc", "-preset", "p2", "-rc", "vbr", "-cq", "24", "-b:v", "0",
                    "-maxrate", "12M", "-bufsize", "24M", "-forced-idr", "1"]),
    ("h264_nvenc", ["-c:v", "h264_nvenc", "-preset", "fast", "-rc", "vbr", "-cq", "24", "-b:v", "0",
                    "-maxrate", "12M", "-bufsize", "24M", "-forced-idr", "1"]),
    ("h264_qsv", ["-c:v", "h264_qsv", "-preset", "veryfast", "-global_quality", "24"]),
    ("h264_amf", ["-c:v", "h264_amf", "-quality", "speed", "-rc", "cqp", "-qp_i", "24", "-qp_p", "24"]),
]


def pick_encoder():
    if not USE_GPU_ENCODER:
        return SOFTWARE_ENCODER
    try:
        listed = run([FFMPEG, "-hide_banner", "-encoders"], 10).stdout
    except Exception:
        return SOFTWARE_ENCODER
    for name, args in GPU_ENCODERS:
        if name not in listed:
            continue
        try:
            test = [FFMPEG, "-hide_banner", "-loglevel", "error", "-f", "lavfi",
                    "-i", "color=c=black:s=1280x720:d=0.3:r=24"] + args + \
                   ["-pix_fmt", "yuv420p", "-f", "null", "-"]
            if run(test, 15).returncode == 0:
                return (name, args)
        except Exception:
            pass
    return SOFTWARE_ENCODER


ENCODER_NAME, ENCODER_ARGS = pick_encoder()


# ============================================================
# NETWORK
# ============================================================

def get_local_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception:
        return "127.0.0.1"


LOCAL_IP = get_local_ip()


# ============================================================
# TITLES & SMALL HELPERS
# ============================================================

_TAGS = re.compile(
    r"\b(2160p|1080p|720p|480p|4k|uhd|bluray|bdrip|brrip|web-?dl|webrip|hdrip|hdtv|dvdrip|"
    r"x264|x265|hevc|h\.?26[45]|10bit|aac|ddp?\d*|dts|atmos|remux|hdr10?|imax|esub|amzn|dsnp)\b",
    re.I,
)
_YEAR = re.compile(r"\b(19\d\d|20\d\d)\b")


def parse_title(filename):
    """'Oppenheimer.2023.1080p.BluRay.x264.mkv' -> ('Oppenheimer', '2023')"""
    stem = Path(filename).stem
    t = re.sub(r"[._]+", " ", stem)
    # drop [YTS.MX] / (1080p) style junk but keep (2023)
    t = re.sub(r"[\[(][^\])]*[\])]",
               lambda m: m.group(0) if re.fullmatch(r"[\[(](19|20)\d\d[\])]", m.group(0)) else " ", t)
    for m in _YEAR.finditer(t):
        prefix = t[:m.start()].strip(" -([")
        if prefix:
            return prefix, m.group(1)
    tag = _TAGS.search(t)
    if tag and t[:tag.start()].strip(" -(["):
        t = t[:tag.start()]
    t = re.sub(r"\s+", " ", t).strip(" -([")
    return (t if len(t) > 1 else stem), ""


def guess_quality(name):
    n = name.lower()
    if "2160p" in n or "4k" in n or "uhd" in n:
        return "4K"
    if "1080p" in n:
        return "1080p"
    if "720p" in n:
        return "720p"
    return ""


# ============================================================
# CATEGORY, SERIES, SEASON & EPISODE DETECTION
# ============================================================

ANIME_SERIES_KEYS = {"anime webseries", "anime series", "animewebseries", "animeseries"}
WEB_SERIES_KEYS = {"hollywood web series", "web series", "tv shows", "tv series", "series", "shows", "webseries"}
ANIME_MOVIE_KEYS = {"anime movies", "animemovies", "anime movie"}
MOVIE_KEYS = {"hollywood movie", "hollywood movies", "movie", "movies"}


def natural_sort_key(s):
    return [int(text) if text.isdigit() else text.lower() for text in re.split(r"(\d+)", str(s))]


def clean_series_name(raw):
    s = raw.strip(" =_-#[](){}")
    if s.upper() in ("ONEPIECE", "ONE PIECE"):
        return "One Piece"
    if s.lower() == "konosuba":
        return "KonoSuba"
    if s.lower() == "naruto":
        return "Naruto"
    if s.lower() == "attack on titan":
        return "Attack on Titan"
    if s.lower() == "code geass":
        return "Code Geass"
    if s.lower() == "sword art online":
        return "Sword Art Online"
    if s.lower() == "fairy tail":
        return "Fairy Tail"
    if s.lower() == "kuruko no basuke":
        return "Kuroko no Basuke"
    s = re.sub(r"[._]+", " ", s).strip()
    return s.title() if s.islower() else s


def clean_season_name(name):
    s = name.strip()
    m = re.match(r"^[sS](\d+)$", s)
    if m:
        return f"Season {int(m.group(1))}"
    if s.isdigit():
        return f"Season {int(s)}"

    m = re.match(r"^(\d+)\.?(.*?)(\d+-\d+)$", s)
    if m:
        num = m.group(1)
        saga_title = m.group(2).strip(" ._-")
        ep_range = m.group(3)
        return f"{num}. {saga_title} ({ep_range})"

    m = re.match(r"^(\d+)\.?(.*?)(\d+-?)$", s)
    if m and any(w in s.lower() for w in ("saga", "arc")):
        num = m.group(1)
        saga_title = m.group(2).strip(" ._-")
        ep_start = m.group(3).rstrip("-")
        return f"{num}. {saga_title} ({ep_start}+)" if ep_start else f"{num}. {saga_title}"

    s = re.sub(r"\bova\b", "OVA", s, flags=re.I)
    s = re.sub(r"\bmovie\b", "Movie", s, flags=re.I)
    return s


def season_sort_key(raw_folder_name):
    """Sort Season 1 -> S1.1 OVA -> Season 2 -> S2.2 Movie -> Season 3, etc."""
    x = str(raw_folder_name).strip()
    m = re.match(r"^[sS](\d+)(.*)", x)
    if m:
        return (int(m.group(1)), 0, natural_sort_key(m.group(2)))
    m = re.match(r"^(\d+)\.?(\d+)?(.*)", x)
    if m:
        major = int(m.group(1))
        minor = int(m.group(2)) if m.group(2) else 0
        return (major, minor, natural_sort_key(m.group(3)))
    return (999, 0, natural_sort_key(x))


def detect_ep_number(filename):
    stem = Path(filename).stem
    m = re.search(r"\b[sS]\d+[._\s-]*[eE](\d{1,4})\b", stem)
    if m:
        return int(m.group(1))
    m = re.search(r"\b\d+x(\d{1,4})\b", stem)
    if m:
        return int(m.group(1))
    m = re.search(r"\b(?:episode|ep)[._\s-]*(\d{1,4})\b", stem, re.I)
    if m:
        return int(m.group(1))
    m = re.search(r"(?:^|\s*-\s*)(\d{1,4})(?:\s*-\s*|\s+|$)", stem)
    if m:
        return int(m.group(1))
    m = re.search(r"^\d+\s+(\d{1,4})\b", stem)
    if m:
        return int(m.group(1))
    m = re.search(r"^\s*(\d{1,4})\b", stem)
    if m:
        return int(m.group(1))
    nums = re.findall(r"\b\d+\b", stem)
    if nums:
        filtered = [int(n) for n in nums if not (len(n) == 4 and (n.startswith("19") or n.startswith("20")))]
        if filtered:
            return filtered[0]
    return 1


def clean_ep_title(stem, ep_num):
    t = re.sub(r"\[[^\]]*\]|\([^\)]*\)", " ", stem)
    t = _TAGS.sub(" ", t)
    t = re.sub(r"[._]+", " ", t).strip(" -([")
    t = re.sub(r"^(?:episode|ep)?[._\s-]*\d+\s*[-.:]?\s*", "", t, flags=re.I).strip()
    t = re.sub(r"@\w+", "", t).strip()
    t = re.sub(r"\s+", " ", t).strip(" -_")
    if not t or len(t) < 2 or t.lower() in ("mkv", "mp4", "avi", "mov", "webm", "flv", "ts", "sub", "dual"):
        return f"Episode {ep_num}"
    return t


def classify_media(rel_path, filename=None):
    p = Path(rel_path)
    filename = filename or p.name
    stem = Path(filename).stem
    parts = list(p.parts)

    norm_parts = parts[1:] if (parts and parts[0].lower() == "movies" and len(parts) > 1) else parts

    cat = "movies"
    is_series = False
    series_name = ""
    sub_parts = []

    for i, part in enumerate(norm_parts[:-1]):
        pl = part.lower()
        if any(k in pl for k in ANIME_SERIES_KEYS):
            cat = "anime_series"
            is_series = True
            if i + 1 < len(norm_parts) - 1:
                series_raw = norm_parts[i + 1]
                sub_parts = norm_parts[i + 2 : -1]
            else:
                series_raw = norm_parts[-2] if len(norm_parts) >= 2 else "Unknown Series"
                sub_parts = []
            series_name = clean_series_name(series_raw)
            break
        elif any(k in pl for k in WEB_SERIES_KEYS):
            cat = "web_series"
            is_series = True
            if i + 1 < len(norm_parts) - 1:
                series_raw = norm_parts[i + 1]
                sub_parts = norm_parts[i + 2 : -1]
            else:
                series_raw = norm_parts[-2] if len(norm_parts) >= 2 else "Unknown Series"
                sub_parts = []
            series_name = clean_series_name(series_raw)
            break
        elif any(k in pl for k in ANIME_MOVIE_KEYS):
            cat = "anime_movies"
            is_series = False
            break
        elif any(k in pl for k in MOVIE_KEYS):
            cat = "movies"
            is_series = False
            break

    if not is_series and cat not in ("anime_movies", "movies"):
        path_str = "/".join(norm_parts).lower()
        if "anime" in path_str:
            if len(norm_parts) >= 3:
                cat = "anime_series"
                is_series = True
                series_name = clean_series_name(norm_parts[1])
                sub_parts = norm_parts[2:-1]
            else:
                cat = "anime_movies"
        else:
            cat = "movies"

    if is_series:
        if sub_parts:
            season_raw = sub_parts[0]
            season_key = season_raw.lower()
            season_name = clean_season_name(season_raw)
        else:
            season_raw = "Season 1"
            season_key = "s1"
            season_name = "Season 1"

        ep_num = detect_ep_number(filename)
        ep_t = clean_ep_title(stem, ep_num)
        arc = sub_parts[1] if len(sub_parts) > 1 else ""
        if arc:
            clean_arc = re.sub(r"^\d+\.\s*", "", arc).strip()
            full_title = f"{clean_arc} • {ep_t}"
        else:
            full_title = ep_t

        return {
            "category": cat,
            "is_series": True,
            "series": series_name,
            "season_raw": season_raw,
            "season_name": season_name,
            "season_key": season_key,
            "season": ep_num,
            "episode": ep_num,
            "ep_title": ep_t,
            "full_title": full_title,
        }
    else:
        parent = norm_parts[-2] if len(norm_parts) >= 2 else ""
        if (
            re.match(r"^(?:ep|episode|vid|track|part|file)[._\s-]*\d*", stem, re.I)
            and parent
            and not any(k in parent.lower() for k in ANIME_MOVIE_KEYS | MOVIE_KEYS)
        ):
            title, year = parse_title(parent)
        else:
            title, year = parse_title(stem)

        return {
            "category": cat,
            "is_series": False,
            "title": title,
            "year": year,
        }


def detect_series(rel_path, filename=None):
    """Backward compatibility wrapper returning dict with is_series, series, season, episode, ep_title."""
    res = classify_media(rel_path, filename)
    if res["is_series"]:
        return {
            "is_series": True,
            "category": res["category"],
            "series": res["series"],
            "season": 1,
            "season_name": res["season_name"],
            "season_key": res["season_key"],
            "season_raw": res.get("season_raw", "Season 1"),
            "episode": res["episode"],
            "ep_title": res["ep_title"],
            "full_title": res["full_title"],
        }
    return {"is_series": False, "category": res.get("category", "movies")}


LANGS = {
    "hin": "Hindi", "hindi": "Hindi", "eng": "English", "english": "English",
    "spa": "Spanish", "fra": "French", "fre": "French", "deu": "German", "ger": "German",
    "ita": "Italian", "jpn": "Japanese", "kor": "Korean", "zho": "Chinese", "chi": "Chinese",
    "tam": "Tamil", "tel": "Telugu", "kan": "Kannada", "mal": "Malayalam", "mar": "Marathi",
    "ben": "Bengali", "rus": "Russian", "por": "Portuguese", "ara": "Arabic", "tur": "Turkish",
}
CHANNELS = {1: "Mono", 2: "Stereo", 6: "5.1", 8: "7.1"}


def audio_label(lang, title, codec, channels, n):
    lang = (lang or "").lower()
    name = LANGS.get(lang)
    if not name:
        name = (title or "").strip()[:26] or (lang.upper() if lang and lang != "und" else f"Track {n}")
    extra = " ".join(x for x in (
        (codec or "").upper().replace("EAC3", "DD+").replace("AC3", "DD"),
        CHANNELS.get(channels, f"{channels}ch" if channels else ""),
    ) if x)
    return f"{name} ({extra})" if extra else name


def fmt_duration(sec):
    sec = int(sec or 0)
    if sec <= 0:
        return ""
    h, m = sec // 3600, (sec % 3600) // 60
    return f"{h}h {m}m" if h else f"{max(m, 1)}m"


def http_msg(text):
    """Status-line messages must be plain ASCII on one line."""
    return str(text).encode("ascii", "replace").decode()[:160].replace("\n", " ").replace("\r", " ")


def rel_of(path):
    return Path(path).relative_to(ROOT).as_posix()


def safe_movie_path(rel):
    """Resolve a library-relative path. Returns None for anything outside the library."""
    if not rel:
        return None
    try:
        p = (ROOT / rel).resolve()
        parts = p.relative_to(ROOT).parts
    except (ValueError, OSError):
        return None
    if p.suffix.lower() not in VIDEO_FORMATS or not p.is_file():
        return None
    if any(x.lower() in IGNORED_DIRS or x.startswith(".") for x in parts[:-1]):
        return None
    return p


# ============================================================
# METADATA CACHE (ffprobe)
# ============================================================

CACHE_VERSION = 3
metadata_cache = {}
cache_lock = threading.Lock()
cache_dirty = False


def load_json(path, default):
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return default


def write_json_atomic(path, obj):
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_suffix(path.suffix + ".tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(obj, f)
        os.replace(tmp, path)
    except Exception as e:
        log(f"Could not write {path.name}: {e}")


def save_cache():
    global cache_dirty
    with cache_lock:
        if not cache_dirty:
            return
        snapshot = dict(metadata_cache)
        cache_dirty = False
    write_json_atomic(CACHE_FILE, snapshot)


def probe_file(path):
    info = {
        "duration": 0.0, "width": 0, "height": 0, "quality": "", "vcodec": "", "pix_fmt": "",
        "bit_rate": 0, "audio": [], "default_audio": None,
    }
    if not FFPROBE:
        return info
    cmd = [
        FFPROBE, "-v", "error", "-show_entries",
        "format=duration,bit_rate:stream=index,codec_type,codec_name,width,height,pix_fmt,channels"
        ":stream_disposition=default:stream_tags=language,title",
        "-of", "json", str(path),
    ]
    try:
        res = run(cmd, 25)
        if res.returncode != 0:
            return info
        data = json.loads(res.stdout or "{}")
    except Exception as e:
        log(f"Probe failed for {path.name}: {e}")
        return info

    for s in data.get("streams", []):
        kind = s.get("codec_type")
        if kind == "video" and not info["vcodec"]:
            w, h = int(s.get("width") or 0), int(s.get("height") or 0)
            info.update(vcodec=(s.get("codec_name") or "").lower(), pix_fmt=s.get("pix_fmt") or "",
                        width=w, height=h)
            info["quality"] = ("4K" if (w >= 3800 or h >= 2100) else "1080p" if (w >= 1900 or h >= 1000)
                               else "720p" if (w >= 1200 or h >= 700) else "SD")
        elif kind == "audio":
            tags = s.get("tags") or {}
            n = len(info["audio"]) + 1
            info["audio"].append({
                "index": s.get("index"),
                "lang": tags.get("language", ""),
                "codec": s.get("codec_name", ""),
                "channels": int(s.get("channels") or 0),
                "default": bool((s.get("disposition") or {}).get("default")),
                "label": audio_label(tags.get("language"), tags.get("title"),
                                     s.get("codec_name"), int(s.get("channels") or 0), n),
            })
    fmt = data.get("format") or {}
    try:
        info["duration"] = float(fmt.get("duration") or 0)
    except ValueError:
        pass
    try:
        info["bit_rate"] = int(fmt.get("bit_rate") or 0)
    except ValueError:
        pass
    if info["audio"]:
        default = next((a for a in info["audio"] if a["default"]), info["audio"][0])
        info["default_audio"] = default["index"]
    if not info["quality"]:
        info["quality"] = guess_quality(path.name)
    return info


def get_meta(path, rel=None, probe=True):
    """Cached metadata; probes with ffprobe on a miss (unless probe=False -> None)."""
    global cache_dirty
    rel = rel or rel_of(path)
    try:
        st = path.stat()
    except OSError:
        return None
    with cache_lock:
        c = metadata_cache.get(rel)
    if c and c.get("v") == CACHE_VERSION and c.get("size") == st.st_size and c.get("mtime") == st.st_mtime:
        return c
    if not probe:
        return None
    info = probe_file(path)
    info.update(v=CACHE_VERSION, size=st.st_size, mtime=st.st_mtime)
    if FFPROBE:
        with cache_lock:
            metadata_cache[rel] = info
            cache_dirty = True
    return info


with cache_lock:
    metadata_cache.update(load_json(CACHE_FILE, {}))


# ============================================================
# THUMBNAILS
# ============================================================

thumb_sem = threading.BoundedSemaphore(2)
thumb_locks = {}
thumb_locks_guard = threading.Lock()
thumb_failed = {}


def get_thumbnail(path, rel, width=640):
    try:
        st = path.stat()
    except OSError:
        return None
    key = hashlib.md5(f"{rel}|{st.st_size}|{int(st.st_mtime)}".encode()).hexdigest()[:20]
    out = THUMBS_DIR / f"{key}_{width}.jpg"
    if out.exists() and out.stat().st_size > 500:
        return out
    if time.time() - thumb_failed.get(out.name, 0) < 600:
        return None
    with thumb_locks_guard:
        lock = thumb_locks.setdefault(out.name, threading.Lock())
    with lock:
        if out.exists() and out.stat().st_size > 500:
            return out
        THUMBS_DIR.mkdir(parents=True, exist_ok=True)
        meta = get_meta(path, rel) or {}
        dur = meta.get("duration") or 0
        first = min(max(dur * 0.12, 8), 600) if dur else 30
        with thumb_sem:
            for t in (first, 3, 0):
                if dur and t >= dur:
                    continue
                cmd = [FFMPEG, "-hide_banner", "-loglevel", "error", "-y", "-ss", f"{t:.2f}",
                       "-i", str(path), "-frames:v", "1", "-an", "-sn",
                       "-vf", f"scale={width}:-2", "-q:v", "4", str(out)]
                try:
                    run(cmd, 30)
                except Exception:
                    pass
                if out.exists() and out.stat().st_size > 500:
                    return out
        thumb_failed[out.name] = time.time()
    return None


FALLBACK_SVG = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 360">
<rect width="640" height="360" fill="#16161a"/><circle cx="320" cy="180" r="42" fill="#ffffff" opacity=".07"/>
<path d="M308 160l34 20-34 20z" fill="#ffffff" opacity=".35"/></svg>"""

FAVICON_SVG = ("<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 32 32'><rect width='32' height='32' rx='8' "
               "fill='#0c0c0f'/><path d='M12 9l12 7-12 7z' fill='#ff7a1a'/></svg>")


# ============================================================
# WATCH PROGRESS (shared between all your devices)
# ============================================================

progress = {}
progress_lock = threading.Lock()
progress_dirty = False
progress_flushed = 0.0


def set_progress(rel, pos, dur, clear=False):
    global progress_dirty
    with progress_lock:
        if clear or (dur > 0 and pos / dur > 0.95) or pos < 10:
            changed = progress.pop(rel, None) is not None
        else:
            progress[rel] = {"pos": int(pos), "dur": int(dur), "ts": int(time.time())}
            changed = True
        progress_dirty = progress_dirty or changed


def flush_progress(force=False):
    global progress_dirty, progress_flushed
    with progress_lock:
        if not progress_dirty or (not force and time.time() - progress_flushed < 3):
            return
        snapshot = dict(progress)
        progress_dirty = False
        progress_flushed = time.time()
    write_json_atomic(PROGRESS_FILE, snapshot)


progress.update(load_json(PROGRESS_FILE, {}))


# ============================================================
# PLAYBACK DECISIONS
# ============================================================

DIRECT_CONTAINERS = {".mp4", ".m4v", ".mov"}


def resolve_audio(meta, audio_index):
    return audio_index if audio_index is not None else meta.get("default_audio")


def can_direct_play(path, meta, audio_index):
    """True when practically every browser can play the file untouched."""
    ext = path.suffix.lower()
    if ext not in DIRECT_CONTAINERS or not meta.get("vcodec"):
        return False
    # Validate container header bytes to reject Matroska / EBML files disguised with .mp4 extension
    try:
        with open(path, "rb") as f:
            header = f.read(16)
        # EBML / Matroska magic bytes (\x1a\x45\xdf\xa3)
        if header.startswith(b"\x1a\x45\xdf\xa3"):
            return False
        # Valid ISO base media file (MP4/MOV) contains 'ftyp' or 'moov' in first 16 bytes
        if b"ftyp" not in header[:16] and b"moov" not in header[:16]:
            return False
    except Exception:
        return False

    if meta.get("bit_rate", 0) > COPY_MAX_BITRATE:
        return False
    tracks = meta.get("audio") or []
    chosen = resolve_audio(meta, audio_index)
    if tracks and chosen != meta.get("default_audio"):
        return False                      # browsers can't switch tracks inside an MP4
    codec = next((a["codec"] for a in tracks if a["index"] == chosen), "") if tracks else ""
    v = meta["vcodec"]
    return v == "h264" and meta.get("pix_fmt") in ("yuv420p", "yuvj420p") and codec in ("", "aac", "mp3")


def pick_video_mode(meta, start_time):
    """'copy' = remux (no re-encode). Only from t=0: seeking into a copied stream is keyframe-inaccurate."""
    if (start_time == 0 and meta.get("vcodec") == "h264"
            and meta.get("pix_fmt") in ("yuv420p", "yuvj420p")
            and 0 < meta.get("height", 0) <= MAX_HEIGHT + 8
            and meta.get("bit_rate", 0) <= COPY_MAX_BITRATE):
        return "copy"
    return "transcode"


# ============================================================
# PROCESS CONTROL (pause / resume ffmpeg without killing it)
# ============================================================

THROTTLE_OK = True


def set_process_paused(pid, pause):
    if os.name == "nt":
        import ctypes
        from ctypes import wintypes
        k32 = ctypes.WinDLL("kernel32", use_last_error=True)
        nt = ctypes.WinDLL("ntdll")
        k32.OpenProcess.restype = wintypes.HANDLE
        k32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
        k32.CloseHandle.argtypes = [wintypes.HANDLE]
        nt.NtSuspendProcess.argtypes = [wintypes.HANDLE]
        nt.NtResumeProcess.argtypes = [wintypes.HANDLE]
        handle = k32.OpenProcess(0x0800, False, pid)      # PROCESS_SUSPEND_RESUME
        if not handle:
            raise OSError("OpenProcess failed")
        try:
            (nt.NtSuspendProcess if pause else nt.NtResumeProcess)(handle)
        finally:
            k32.CloseHandle(handle)
    else:
        import signal
        os.kill(pid, signal.SIGSTOP if pause else signal.SIGCONT)


# ============================================================
# HLS JOBS
# ============================================================

jobs = {}
jobs_lock = threading.Lock()
session_seq = {}          # sid -> (latest request number, timestamp)


class HLSJob:
    def __init__(self, sid, movie, rel, audio_index, start_time, meta):
        self.id = uuid.uuid4().hex
        self.sid, self.movie, self.rel = sid, movie, rel
        self.audio = resolve_audio(meta, audio_index)
        self.start_time = int(start_time)
        self.meta = meta
        self.mode = pick_video_mode(meta, self.start_time)
        self.dir = HLS_DIR / self.id
        self.playlist = self.dir / "index.m3u8"
        self.proc = None
        self.stopped = self.finished = self.suspended = False
        self.error = None
        self.last_access = time.time()
        self.last_req = 0
        self.stderr_tail = collections.deque(maxlen=25)

    # ---- ffmpeg command -------------------------------------------------
    def build_cmd(self):
        cmd = [FFMPEG, "-nostdin", "-hide_banner", "-loglevel", "error", "-y"]
        if self.start_time > 0:
            cmd += ["-ss", str(self.start_time)]
        cmd += ["-i", str(self.movie), "-map", "0:v:0"]
        if self.mode == "copy":
            cmd += ["-c:v", "copy"]
        else:
            cmd += ["-vf", f"scale=-2:'min({MAX_HEIGHT},ih)'"] + ENCODER_ARGS + [
                "-pix_fmt", "yuv420p",
                "-force_key_frames", f"expr:gte(t,n_forced*{SEGMENT_TIME})",
            ]
        cmd += ["-map", f"0:{self.audio}" if self.audio is not None else "0:a:0?",
                "-c:a", "aac", "-b:a", "192k", "-ac", "2",
                "-sn", "-dn", "-max_muxing_queue_size", "1024",
                "-f", "hls", "-hls_time", str(SEGMENT_TIME),
                # EVENT = "starts at the beginning, grows while encoding" (a plain
                # playlist is treated as LIVE, and players jump to the end of it)
                "-hls_playlist_type", "event",
                "-hls_flags", "independent_segments",
                "-hls_segment_filename", str(self.dir / "seg_%05d.ts"),
                str(self.playlist)]
        return cmd

    def start(self):
        self.dir.mkdir(parents=True, exist_ok=True)
        label = {"copy": "remux", "transcode": f"transcode ({ENCODER_NAME})"}[self.mode]
        log(f"stream  {label:<26} {self.rel}  @{self.start_time}s")
        try:
            self.proc = subprocess.Popen(
                self.build_cmd(), stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE, text=True, encoding="utf-8", errors="replace",
                creationflags=NO_WINDOW,
            )
        except Exception as e:
            self.error = str(e)
            log(f"Could not start ffmpeg: {e}")
            return
        threading.Thread(target=self._watch, daemon=True).start()

    def _watch(self):
        rc = -1
        try:
            for line in self.proc.stderr:
                self.stderr_tail.append(line.rstrip())
            rc = self.proc.wait()
        except Exception as e:
            self.stderr_tail.append(str(e))
        if self.stopped:
            return
        if rc == 0:
            self.finished = True
        else:
            self.error = " | ".join(list(self.stderr_tail)[-4:]) or f"ffmpeg exited with code {rc}"
            log(f"ffmpeg error ({self.rel}): {self.error}")

    # ---- lifecycle ------------------------------------------------------
    def touch(self):
        self.last_access = time.time()

    def count_segments(self):
        try:
            return sum(1 for e in os.scandir(self.dir) if e.name.endswith(".ts"))
        except OSError:
            return 0

    def stop(self):
        if self.stopped:
            return
        self.stopped = True
        p = self.proc
        if p and p.poll() is None:
            try:
                p.kill()
            except Exception:
                pass
        threading.Thread(target=self._cleanup, daemon=True).start()

    def _cleanup(self):
        if self.proc:
            try:
                self.proc.wait(timeout=10)
            except Exception:
                pass
        for _ in range(8):                       # Windows may still hold a file for a moment
            shutil.rmtree(self.dir, ignore_errors=True)
            if not self.dir.exists():
                break
            time.sleep(1)

    def housekeeping(self, now):
        """Called every second. Returns True when the job should be removed."""
        global THROTTLE_OK
        if self.stopped:
            return True
        if now - self.last_access > IDLE_TIMEOUT:
            return True
        p = self.proc
        if not (THROTTLE_OK and p and p.poll() is None):
            return False
        limit = max(8, BUFFER_AHEAD_SECONDS // SEGMENT_TIME)
        ahead = self.count_segments() - self.last_req
        try:
            if not self.suspended and ahead > limit:
                set_process_paused(p.pid, True)
                self.suspended = True
            elif self.suspended and ahead < limit * 0.6:
                set_process_paused(p.pid, False)
                self.suspended = False
        except Exception as e:
            THROTTLE_OK = False
            log(f"Throttling disabled ({e})")
        return False


def start_job(sid, seq, movie, rel, audio_index, start_time, meta):
    """Start a stream for a player session, replacing that session's previous one."""
    with jobs_lock:
        prev_seq = session_seq.get(sid, (0, 0))[0]
        if seq < prev_seq:
            return None                          # an older request that lost a race
        session_seq[sid] = (seq, time.time())
        old = [j for j in jobs.values() if j.sid == sid]
        for j in old:
            jobs.pop(j.id, None)
        job = HLSJob(sid, movie, rel, audio_index, start_time, meta)
        jobs[job.id] = job
    for j in old:
        j.stop()
    job.start()
    return job


def stop_session(sid, seq=None):
    with jobs_lock:
        if seq is not None:
            if seq < session_seq.get(sid, (0, 0))[0]:
                return False
            session_seq[sid] = (seq, time.time())
        old = [j for j in jobs.values() if j.sid == sid]
        for j in old:
            jobs.pop(j.id, None)
    for j in old:
        j.stop()
    return True


def stop_all_jobs():
    with jobs_lock:
        old = list(jobs.values())
        jobs.clear()
    for j in old:
        j.stop()


def cleanup_stale_dirs():
    """Delete job folders left behind by a previous run."""
    try:
        for e in os.scandir(HLS_DIR):
            if e.is_dir() and re.fullmatch(r"[0-9a-f]{32}", e.name):
                shutil.rmtree(e.path, ignore_errors=True)
    except OSError:
        pass


def janitor_loop():
    last_prune = 0
    while True:
        time.sleep(1)
        now = time.time()
        with jobs_lock:
            items = list(jobs.values())
        for j in items:
            try:
                if j.housekeeping(now):
                    with jobs_lock:
                        jobs.pop(j.id, None)
                    j.stop()
            except Exception as e:
                log(f"janitor: {e}")
        flush_progress()
        save_cache()
        if now - last_prune > 300:
            last_prune = now
            with jobs_lock:
                for sid in [s for s, (_, ts) in session_seq.items() if now - ts > 21600]:
                    session_seq.pop(sid, None)


# ============================================================
# LIBRARY SCAN
# ============================================================

_list_cache = {"t": 0.0, "items": []}
_list_lock = threading.Lock()
scan = {"running": False, "probing": False, "last": 0.0, "done": 0, "total": 0}
scan_lock = threading.Lock()


def list_movies():
    with _list_lock:
        if time.time() - _list_cache["t"] < 4:
            return _list_cache["items"]
        items = []
        for root, dirs, files in os.walk(ROOT):
            dirs[:] = sorted(d for d in dirs if d.lower() not in IGNORED_DIRS and not d.startswith("."))
            for f in sorted(files):
                if f.startswith(".") or os.path.splitext(f)[1].lower() not in VIDEO_FORMATS:
                    continue
                p = Path(root) / f
                items.append((p, p.relative_to(ROOT).as_posix()))
        _list_cache.update(t=time.time(), items=items)
        return items


def _scan_worker():
    try:
        items = list_movies()
        todo = [it for it in items if get_meta(it[0], it[1], probe=False) is None]
        scan.update(total=len(todo), done=0, probing=bool(todo))

        def work(it):
            try:
                get_meta(*it)
            except Exception as e:
                log(f"probe error {it[1]}: {e}")
            finally:
                scan["done"] += 1

        with ThreadPoolExecutor(max_workers=PROBE_WORKERS) as ex:
            list(ex.map(work, todo))
        scan["probing"] = False
        save_cache()
        with ThreadPoolExecutor(max_workers=2) as ex:      # warm the thumbnail cache
            list(ex.map(lambda it: get_thumbnail(it[0], it[1]), items))
    except Exception as e:
        log(f"scan error: {e}")
    finally:
        scan.update(running=False, probing=False, last=time.time())


def ensure_scan(force=False):
    with scan_lock:
        if scan["running"] or (not force and time.time() - scan["last"] < 30):
            return
        scan["running"] = True
    threading.Thread(target=_scan_worker, daemon=True).start()


_lib_cache = {"t": 0.0, "data": None}
_lib_lock = threading.Lock()


def build_library_data():
    ensure_scan()
    with _lib_lock:
        if time.time() - _lib_cache["t"] < 3 and _lib_cache["data"]:
            return _lib_cache["data"]

    items = list_movies()
    anime_series_map = {}
    web_series_map = {}
    anime_movies = []
    movies = []
    all_items = []
    total_size = 0

    for p, rel in items:
        try:
            st = p.stat()
        except OSError:
            continue
        total_size += st.st_size
        m = get_meta(p, rel, probe=False)
        parent = rel.rsplit("/", 1)[0] if "/" in rel else ""
        c_info = classify_media(rel, p.name)

        if c_info["is_series"]:
            title = c_info["full_title"]
            year = ""
        else:
            title = c_info.get("title") or parse_title(p.name)[0]
            year = c_info.get("year") or parse_title(p.name)[1]

        item = {
            "path": rel, "file": p.name, "title": title, "year": year, "folder": parent,
            "ext": p.suffix.lower(), "size": st.st_size, "mtime": int(st.st_mtime),
            "added": int(st.st_ctime if os.name == "nt" else st.st_mtime),
            "ready": bool(m),
            "duration": round(m["duration"]) if m else 0,
            "quality": (m["quality"] if m else guess_quality(p.name)),
            "vcodec": m["vcodec"].upper() if m else "",
            "audio": [a["label"] for a in m["audio"]] if m else [],
            "progress": progress.get(rel),
            "category": c_info["category"],
            "isSeries": c_info["is_series"],
            "seriesInfo": c_info if c_info["is_series"] else None,
        }
        all_items.append(item)

        if c_info["is_series"]:
            s_name = c_info["series"]
            target_map = anime_series_map if c_info["category"] == "anime_series" else web_series_map
            if s_name not in target_map:
                target_map[s_name] = {
                    "id": hashlib.md5(f"{c_info['category']}:{s_name.lower()}".encode()).hexdigest()[:12],
                    "title": s_name,
                    "category": c_info["category"],
                    "year": year,
                    "folder": parent,
                    "seasons": {},
                    "totalEpisodes": 0,
                    "totalSize": 0,
                    "quality": item["quality"],
                    "posterPath": rel,
                    "added": item["added"],
                    "latestProgress": None,
                }
            s_entry = target_map[s_name]
            s_entry["totalEpisodes"] += 1
            s_entry["totalSize"] += item["size"]
            if item["added"] > s_entry["added"]:
                s_entry["added"] = item["added"]
            if item["quality"] == "4K" or (item["quality"] == "1080p" and s_entry["quality"] != "4K"):
                s_entry["quality"] = item["quality"]

            sea_key = c_info["season_key"]
            if sea_key not in s_entry["seasons"]:
                s_entry["seasons"][sea_key] = {
                    "id": f"{s_entry['id']}_{hashlib.md5(sea_key.encode()).hexdigest()[:6]}",
                    "raw": c_info["season_raw"],
                    "name": c_info["season_name"],
                    "seasonName": c_info["season_name"],
                    "seasonNumber": 1,
                    "episodes": [],
                }
            ep_item = {
                "episodeNumber": c_info["episode"],
                "seasonId": s_entry["seasons"][sea_key]["id"],
                "seasonName": c_info["season_name"],
                "title": c_info["ep_title"],
                "fullTitle": c_info["full_title"],
                "path": rel,
                "file": p.name,
                "duration": item["duration"],
                "quality": item["quality"],
                "size": item["size"],
                "audio": item["audio"],
                "progress": item["progress"],
            }
            s_entry["seasons"][sea_key]["episodes"].append(ep_item)
            if item["progress"]:
                if not s_entry["latestProgress"] or item["progress"]["ts"] > s_entry["latestProgress"]["ts"]:
                    s_entry["latestProgress"] = {
                        "path": rel,
                        "seasonId": s_entry["seasons"][sea_key]["id"],
                        "seasonName": c_info["season_name"],
                        "episode": c_info["episode"],
                        "epTitle": c_info["ep_title"],
                        "pos": item["progress"]["pos"],
                        "dur": item["progress"]["dur"],
                        "ts": item["progress"]["ts"],
                    }
        else:
            if c_info["category"] == "anime_movies":
                anime_movies.append(item)
            else:
                movies.append(item)

    def process_series_map(s_map):
        series_list = []
        for s_name, s_data in s_map.items():
            sorted_seasons = sorted(s_data["seasons"].values(), key=lambda x: season_sort_key(x["raw"]))
            for s_idx, season in enumerate(sorted_seasons):
                season["seasonNumber"] = s_idx + 1
                season["episodes"].sort(key=lambda x: (x["episodeNumber"], natural_sort_key(x["file"])))

            for s_idx, season in enumerate(sorted_seasons):
                for e_idx, ep in enumerate(season["episodes"]):
                    if e_idx + 1 < len(season["episodes"]):
                        ep["nextEpisodePath"] = season["episodes"][e_idx + 1]["path"]
                    elif s_idx + 1 < len(sorted_seasons) and sorted_seasons[s_idx + 1]["episodes"]:
                        ep["nextEpisodePath"] = sorted_seasons[s_idx + 1]["episodes"][0]["path"]
                    else:
                        ep["nextEpisodePath"] = None

            if sorted_seasons and sorted_seasons[0]["episodes"]:
                s_data["posterPath"] = sorted_seasons[0]["episodes"][0]["path"]

            s_data["seasons"] = sorted_seasons
            s_data["seasonsCount"] = len(sorted_seasons)
            series_list.append(s_data)

        series_list.sort(key=lambda x: x["title"].lower())
        return series_list

    anime_series = process_series_map(anime_series_map)
    web_series = process_series_map(web_series_map)
    all_series = anime_series + web_series
    all_movies = movies + anime_movies

    anime_movies.sort(key=lambda x: x["title"].lower())
    movies.sort(key=lambda x: x["title"].lower())

    res = {
        "movies": movies,
        "anime_movies": anime_movies,
        "all_movies": all_movies,
        "anime_series": anime_series,
        "web_series": web_series,
        "all_series": all_series,
        "series": all_series,
        "all_items": all_items,
        "total_size": total_size,
    }
    with _lib_lock:
        _lib_cache.update(t=time.time(), data=res)
    return res


def library_payload():
    d = build_library_data()
    return {
        "app": APP_NAME,
        "anime_series": d["anime_series"],
        "web_series": d["web_series"],
        "anime_movies": d["anime_movies"],
        "movies": d["movies"],
        "all_series": d["all_series"],
        "all_movies": d["all_movies"],
        "series": d["all_series"],
        "all_items": d["all_items"],
        "total_size": d["total_size"],
        "root": str(ROOT),
        "scanning": scan["probing"],
        "scanned": scan["done"],
        "to_scan": scan["total"],
        "ip": LOCAL_IP,
        "port": PORT,
    }


# ============================================================
# HLS.JS (served locally; falls back to the CDN until downloaded)
# ============================================================

def fetch_hls_js():
    if HLS_JS_FILE.exists():
        return
    try:
        HLS_DIR.mkdir(parents=True, exist_ok=True)
        with urllib.request.urlopen(HLS_JS_CDN, timeout=20) as r:
            data = r.read()
        if len(data) > 100_000:
            HLS_JS_FILE.write_bytes(data)
            log("Downloaded hls.js for offline use")
    except Exception as e:
        log(f"Could not cache hls.js ({e}); the CDN copy will be used")


# ============================================================
# WEB PAGES (templates live below)
# ============================================================

def render_home():
    return (HOME_HTML.replace("__APP__", escape(APP_NAME)))


def render_player(movie, rel, query):
    meta = get_meta(movie, rel) or {}
    prog = progress.get(rel) or {}
    c_info = classify_media(rel, movie.name)

    next_ep = None
    if c_info["is_series"]:
        lib = build_library_data()
        for s in lib["all_series"]:
            if s["title"].lower() == c_info["series"].lower():
                for season in s["seasons"]:
                    for ep in season["episodes"]:
                        if ep["path"] == rel:
                            next_ep = ep.get("nextEpisodePath")
                            break

    title = c_info.get("full_title") if c_info["is_series"] else (c_info.get("title") or parse_title(movie.name)[0])
    year = "" if c_info["is_series"] else (c_info.get("year") or parse_title(movie.name)[1])

    cfg = {
        "path": rel, "title": title, "year": year, "file": movie.name, "app": APP_NAME,
        "duration": round(meta.get("duration") or 0, 2),
        "quality": meta.get("quality") or guess_quality(movie.name),
        "audio": [{"index": a["index"], "label": a["label"]} for a in meta.get("audio", [])],
        "defaultAudio": meta.get("default_audio"),
        "resume": prog.get("pos", 0),
        "isSeries": c_info["is_series"],
        "seriesTitle": c_info.get("series", "") if c_info["is_series"] else "",
        "season": c_info.get("season", 0) if c_info["is_series"] else 0,
        "seasonName": c_info.get("season_name", "") if c_info["is_series"] else "",
        "episode": c_info.get("episode", 0) if c_info["is_series"] else 0,
        "epTitle": c_info.get("ep_title", "") if c_info["is_series"] else "",
        "nextEpisode": next_ep,
    }
    blob = json.dumps(cfg).replace("<", "\\u003c").replace("\u2028", "\\u2028").replace("\u2029", "\\u2029")
    page_title = f"{c_info['series']} - {c_info.get('season_name', '')} Ep {c_info['episode']}" if c_info["is_series"] else title
    return (PLAYER_HTML.replace("__APP__", escape(APP_NAME))
            .replace("__PAGE_TITLE__", escape(page_title))
            .replace("__CONFIG__", blob))


# ============================================================
# HTTP SERVER
# ============================================================

class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"           # keep-alive: much faster for HLS segments
    server_version = "Cinema/2.0"

    def log_message(self, fmt, *args):
        pass

    def log_request(self, code="-", size="-"):
        try:
            if int(code) >= 400 and "/thumb" not in self.path:
                log(f"{code} {self.command} {unquote(self.path)[:120]}")
        except ValueError:
            pass

    # ---- low level helpers ---------------------------------------------
    def send_bytes(self, data, ctype, status=200, cache="no-cache", extra=None):
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", cache)
        self.send_header("Access-Control-Allow-Origin", "*")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(data)

    def send_json(self, obj, status=200):
        self.send_bytes(json.dumps(obj).encode("utf-8"), "application/json", status, cache="no-store")

    def serve_file(self, path, ctype, cache="no-cache"):
        """Static file with HTTP Range support (needed by Safari, VLC and <video>)."""
        size = path.stat().st_size
        start, end, status = 0, size - 1, 200
        rng = self.headers.get("Range")
        if rng:
            m = re.match(r"bytes=(\d*)-(\d*)", rng.strip())
            if m and (m.group(1) or m.group(2)):
                a, b = m.groups()
                if a == "":
                    start = max(0, size - int(b))
                else:
                    start = int(a)
                    end = min(int(b), size - 1) if b else size - 1
                if start > end or start >= size:
                    self.send_response(416)
                    self.send_header("Content-Range", f"bytes */{size}")
                    self.send_header("Content-Length", "0")
                    self.end_headers()
                    return
                status = 206
        length = end - start + 1
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(length))
        self.send_header("Accept-Ranges", "bytes")
        self.send_header("Cache-Control", cache)
        self.send_header("Access-Control-Allow-Origin", "*")
        if status == 206:
            self.send_header("Content-Range", f"bytes {start}-{end}/{size}")
        self.end_headers()
        if self.command == "HEAD":
            return
        with open(path, "rb") as f:
            f.seek(start)
            left = length
            while left > 0:
                chunk = f.read(min(256 * 1024, left))
                if not chunk:
                    break
                self.wfile.write(chunk)
                left -= len(chunk)

    # ---- routing ----------------------------------------------------------
    def do_HEAD(self):
        self.do_GET()

    def do_GET(self):
        try:
            u = urlparse(self.path)
            path = unquote(u.path)
            q = {k: v[0] for k, v in parse_qs(u.query).items()}

            if path in ("/", "/index.html"):
                return self.send_bytes(render_home().encode("utf-8"), "text/html; charset=utf-8")
            if path == "/api/library":
                return self.send_json(library_payload())
            if path == "/api/start":
                return self.api_start(q)
            if path.startswith("/thumb/"):
                return self.serve_thumb(path[len("/thumb/"):], q)
            if path == "/thumb-fallback":
                return self.send_bytes(FALLBACK_SVG.encode(), "image/svg+xml", cache="public, max-age=86400")
            if path.startswith("/player/"):
                rel = path[len("/player/"):]
                movie = safe_movie_path(rel)
                if not movie:
                    return self.send_error(404, "Movie not found")
                return self.send_bytes(render_player(movie, rel_of(movie), q).encode("utf-8"), "text/html; charset=utf-8")
            if path.startswith("/hls/"):
                return self.serve_hls(path)
            if path.startswith("/stream/"):
                movie = safe_movie_path(path[len("/stream/"):])
                if not movie:
                    return self.send_error(404, "Movie not found")
                ctype = MIME.get(movie.suffix.lower(), "application/octet-stream")
                return self.serve_file(movie, ctype)
            if path == "/static/hls.js":
                if HLS_JS_FILE.exists():
                    return self.serve_file(HLS_JS_FILE, "application/javascript", cache="public, max-age=604800")
                self.send_response(302)
                self.send_header("Location", HLS_JS_CDN)
                self.send_header("Content-Length", "0")
                self.end_headers()
                return
            if path in ("/favicon.ico", "/favicon.svg"):
                return self.send_bytes(FAVICON_SVG.encode(), "image/svg+xml", cache="public, max-age=86400")
            self.send_error(404, "Not Found")
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError, TimeoutError):
            pass
        except Exception as e:
            log(f"Request error ({self.path[:80]}): {e}")
            try:
                self.send_error(500, http_msg(e))
            except Exception:
                pass

    def do_POST(self):
        try:
            n = int(self.headers.get("Content-Length") or 0)
            raw = self.rfile.read(min(n, 65536)) if n else b""
            try:
                body = json.loads(raw.decode("utf-8") or "{}")
            except ValueError:
                body = {}
            path = unquote(urlparse(self.path).path)
            if path == "/api/progress":
                rel = body.get("path", "")
                if safe_movie_path(rel):
                    set_progress(rel, float(body.get("pos") or 0), float(body.get("dur") or 0),
                                 clear=bool(body.get("clear")))
                return self.send_json({"ok": True})
            if path == "/api/stop":
                stop_session(str(body.get("sid", ""))[:64])
                return self.send_json({"ok": True})
            self.send_error(404)
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError, TimeoutError):
            pass
        except Exception as e:
            log(f"POST error: {e}")
            try:
                self.send_error(500, http_msg(e))
            except Exception:
                pass

    # ---- endpoints --------------------------------------------------------
    def serve_thumb(self, rel, q):
        movie = safe_movie_path(rel)
        if not movie:
            return self.send_error(404, "Movie not found")
        width = 1280 if q.get("w") == "1280" else 640
        thumb = get_thumbnail(movie, rel_of(movie), width)
        if thumb:
            return self.serve_file(thumb, "image/jpeg", cache="public, max-age=604800")
        self.send_bytes(FALLBACK_SVG.encode(), "image/svg+xml", cache="no-cache")

    def api_start(self, q):
        rel = q.get("movie", "")
        movie = safe_movie_path(rel)
        if not movie:
            return self.send_json({"status": "error", "error": "Movie not found"}, 404)
        sid = (q.get("sid") or "anon")[:64]
        try:
            seq = int(q.get("seq") or 1)
            start = max(0, int(float(q.get("t") or 0)))
            audio = int(q["audio"]) if q.get("audio", "").lstrip("-").isdigit() else None
        except ValueError:
            return self.send_json({"status": "error", "error": "Bad parameters"}, 400)
        meta = get_meta(movie, rel_of(movie)) or {}
        url_rel = quote(rel_of(movie))
        if FFPROBE and not meta.get("vcodec"):
            return self.send_json({"status": "error",
                                   "error": "This file can't be read. It may be corrupt, or still copying."})

        if q.get("mode") != "hls" and can_direct_play(movie, meta, audio):
            if not stop_session(sid, seq):
                return self.send_json({"status": "stale"})
            return self.send_json({"status": "ok", "mode": "direct", "how": "direct",
                                   "url": f"/stream/{url_rel}", "startTime": 0})

        job = start_job(sid, seq, movie, rel_of(movie), audio, start, meta)
        if job is None:
            return self.send_json({"status": "stale"})
        # give ffmpeg a moment: report an immediate failure now instead of letting the player retry for a minute
        deadline = time.time() + 1.5
        while time.time() < deadline and not job.error:
            if job.playlist.exists():
                break
            time.sleep(0.03)
        if job.error:
            stop_session(sid)
            return self.send_json({"status": "error", "error": "ffmpeg could not process this file. " + http_msg(job.error)[:120]})
        self.send_json({"status": "ok", "mode": "hls", "how": job.mode,
                        "url": f"/hls/{job.id}/index.m3u8", "startTime": job.start_time})

    def serve_hls(self, path):
        parts = path.split("/")                       # ['', 'hls', job, file]
        if len(parts) != 4 or not re.fullmatch(r"index\.m3u8|seg_\d{5}\.ts", parts[3]):
            return self.send_error(404)
        with jobs_lock:
            job = jobs.get(parts[2])
        if not job or job.stopped:
            return self.send_error(404, "Stream expired")
        job.touch()
        name = parts[3]
        fp = job.dir / name

        if name == "index.m3u8":
            deadline = time.time() + 45
            while time.time() < deadline:
                if job.error:
                    return self.send_error(500, http_msg(job.error))
                if job.stopped:
                    return self.send_error(404, "Stream expired")
                try:
                    data = fp.read_bytes()
                    if data.startswith(b"#EXTM3U") and b"#EXTINF" in data and data.endswith(b"\n"):
                        return self.send_bytes(data, "application/vnd.apple.mpegurl", cache="no-store")
                except OSError:
                    pass
                time.sleep(0.04)
            return self.send_error(504, "Stream is taking too long to start")

        job.last_req = int(name[4:9])
        if not fp.exists():
            return self.send_error(404, "Segment not found")
        self.serve_file(fp, "video/mp2t", cache="no-store")


class QuietServer(ThreadingHTTPServer):
    daemon_threads = True
    request_queue_size = 64


# ============================================================
# MAIN
# ============================================================

def main():
    HLS_DIR.mkdir(parents=True, exist_ok=True)
    THUMBS_DIR.mkdir(parents=True, exist_ok=True)
    cleanup_stale_dirs()
    atexit.register(stop_all_jobs)
    atexit.register(lambda: (flush_progress(True), save_cache()))

    threading.Thread(target=janitor_loop, daemon=True).start()
    threading.Thread(target=fetch_hls_js, daemon=True).start()
    ensure_scan(force=True)

    print()
    print("=" * 62)
    print(f"  {APP_NAME.upper()}  -  personal streaming server")
    print("=" * 62)
    print(f"  Library    {ROOT}")
    print(f"  ffmpeg     {FFMPEG}")
    print(f"  ffprobe    {FFPROBE or 'not found (limited features)'}")
    print(f"  Encoder    {ENCODER_NAME}" + ("  (GPU)" if ENCODER_NAME != "libx264" else "  (CPU)"))
    print(f"  This PC    http://localhost:{PORT}")
    print(f"  iPad/phone http://{LOCAL_IP}:{PORT}")
    print("=" * 62)
    print("  Press CTRL+C to stop.\n")

    server = QuietServer(("0.0.0.0", PORT), Handler)
    import signal
    for sig_name in ("SIGTERM", "SIGBREAK"):          # closing the window / `kill` also stops ffmpeg cleanly
        if hasattr(signal, sig_name):
            try:
                signal.signal(getattr(signal, sig_name), lambda *_: sys.exit(0))
            except (ValueError, OSError):
                pass
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopping...")
    finally:
        stop_all_jobs()
        flush_progress(True)
        save_cache()
        server.server_close()
        time.sleep(0.5)


# ============================================================
# PAGE TEMPLATES
# ============================================================

HOME_HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#0c0c0f">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="mobile-web-app-capable" content="yes">
<title>__APP__</title>
<link rel="icon" href="/favicon.svg" type="image/svg+xml">
<style>
:root{
  --bg:#0c0c0f; --panel:#16161a; --line:#ffffff14; --text:#f3f3f5; --muted:#9b9ba5;
  --accent:#ff7a1a; --series:#8b5cf6; --pad:max(4vw,20px); --ease:cubic-bezier(.22,.8,.24,1);
  --font:-apple-system,BlinkMacSystemFont,"SF Pro Display","Segoe UI Variable Display","Segoe UI",Roboto,Helvetica,Arial,sans-serif;
}
*{box-sizing:border-box;margin:0;padding:0}
html{-webkit-text-size-adjust:100%;scroll-behavior:smooth}
body{background:var(--bg);color:var(--text);font:400 15px/1.45 var(--font);min-height:100vh;overflow-x:hidden;-webkit-font-smoothing:antialiased}
a{color:inherit;text-decoration:none}
[hidden]{display:none!important}
button,select{font:inherit;color:inherit;background:none;border:0;cursor:pointer}
:focus-visible{outline:2px solid var(--accent);outline-offset:3px;border-radius:6px}
svg.i{width:20px;height:20px;fill:none;stroke:currentColor;stroke-width:2;stroke-linecap:round;stroke-linejoin:round;flex:none}
svg.i.f{fill:currentColor;stroke:none}

/* ---------- navigation ---------- */
.nav{position:fixed;inset:0 0 auto;z-index:50;height:64px;padding:0 var(--pad);padding-top:env(safe-area-inset-top);box-sizing:content-box;display:flex;align-items:center;gap:26px;
  background:linear-gradient(#000000d9,#0000);transition:background .35s,box-shadow .35s}
.nav.solid{background:#0c0c0fe6;backdrop-filter:blur(18px);-webkit-backdrop-filter:blur(18px);box-shadow:0 1px 0 var(--line)}
.logo{font-weight:900;font-size:21px;letter-spacing:.16em;color:var(--accent);padding:4px 0;display:flex;align-items:center;gap:6px}
.logo span{color:#fff}
.nav-links{display:flex;align-items:center;gap:20px}
.nav .lnk{color:var(--muted);font-size:14.5px;font-weight:500;padding:6px 2px;position:relative;transition:color .2s}
.nav .lnk:hover{color:#fff}
.nav .lnk.on{color:#fff;font-weight:700}
.nav .lnk.on::after{content:"";position:absolute;left:0;right:0;bottom:-4px;height:2.5px;background:var(--accent);border-radius:2px}
.grow{flex:1}
.search{display:flex;align-items:center;border:1px solid transparent;border-radius:8px;transition:background .3s,border-color .3s}
.search.open{background:#000000b3;border-color:#ffffff40}
.search input{width:0;opacity:0;padding:0;background:none;border:0;outline:0;color:#fff;font:inherit;transition:width .4s var(--ease),opacity .25s,padding .4s var(--ease)}
.search.open input{width:min(280px,44vw);opacity:1;padding:9px 12px 9px 0}
.ib{width:42px;height:42px;display:grid;place-items:center;border-radius:50%;transition:background .2s,transform .2s}
.ib:hover{background:#ffffff1f}.ib:active{transform:scale(.92)}

/* ---------- hero carousel ---------- */
.hero{position:relative;height:min(88vh,780px);min-height:480px;overflow:hidden;background:var(--panel)}
.hero-carousel{position:relative;width:100%;height:100%;overflow:hidden}
.hero-track{display:flex;width:100%;height:100%;overflow-x:auto;scroll-snap-type:x mandatory;scroll-behavior:smooth;-webkit-overflow-scrolling:touch;scrollbar-width:none}
.hero-track::-webkit-scrollbar{display:none}

.hero-slide{position:relative;flex:0 0 100%;width:100%;height:100%;scroll-snap-align:start;scroll-snap-stop:always;display:flex;align-items:flex-end;overflow:hidden}
.hero-slide .bg{position:absolute;inset:0;width:100%;height:100%;object-fit:cover;opacity:0;transform:scale(1.03);transition:opacity 0.8s ease}
.hero-slide .bg.ld{opacity:.88}
.hero-slide.active .bg.ld{animation:drift 30s ease-out forwards}
@keyframes drift{to{transform:scale(1.13)}}

.hero-slide::before{content:"";position:absolute;inset:0;z-index:1;background:
  linear-gradient(90deg,#0c0c0ff2 0%,#0c0c0f94 36%,#0c0c0f00 68%),linear-gradient(0deg,var(--bg) 0%,#0c0c0f00 42%),linear-gradient(180deg,#0c0c0f88 0,#0c0c0f00 22%)}

.hero-c{position:relative;z-index:2;padding:0 var(--pad) clamp(70px,13vh,125px);max-width:min(820px,100%)}
.hero-slide.active .hero-c>*{animation:rise .8s var(--ease) both}
.hero-slide.active .hero-c>:nth-child(2){animation-delay:.08s}
.hero-slide.active .hero-c>:nth-child(3){animation-delay:.16s}
.hero-slide.active .hero-c>:nth-child(4){animation-delay:.24s}
@keyframes rise{from{opacity:0;transform:translateY(24px)}to{opacity:1;transform:none}}

.why{color:#ffffffbf;font-size:14px;font-weight:600;margin-bottom:12px;display:flex;align-items:center;gap:10px}
.why::before{content:"";width:4px;height:18px;border-radius:2px;background:var(--accent)}
.hero h1{font-size:clamp(34px,6.2vw,74px);line-height:1.05;font-weight:800;letter-spacing:-.035em;text-wrap:balance;text-shadow:0 4px 30px #000a}
.facts{display:flex;flex-wrap:wrap;align-items:center;gap:6px 18px;margin:18px 0 24px;color:#ffffffc7;font-size:15px;font-weight:500}
.facts .q{padding:2px 8px;border:1px solid #ffffff66;border-radius:4px;font-size:12px;font-weight:700}
.btns{display:flex;flex-wrap:wrap;gap:12px}
.btn{display:inline-flex;align-items:center;gap:10px;padding:12px 26px;border-radius:8px;font-weight:700;font-size:15.5px;transition:transform .2s,background .2s}
.btn:active{transform:scale(.96)}
.btn.pri{background:#fff;color:#000}.btn.pri:hover{background:#ffffffd4}
.btn.ghost{background:#6e6e73b3;color:#fff;backdrop-filter:blur(10px);-webkit-backdrop-filter:blur(10px)}.btn.ghost:hover{background:#6e6e7388}
.hero-bar{height:3px;width:min(260px,70%);background:#ffffff40;border-radius:2px;margin:-8px 0 24px;overflow:hidden}
.hero-bar i{display:block;height:100%;background:var(--accent)}

/* Hero Carousel Controls */
.hero-arrow{position:absolute;top:50%;transform:translateY(-50%);z-index:12;width:48px;height:48px;border-radius:50%;background:#00000088;color:#fff;display:grid;place-items:center;cursor:pointer;border:1px solid #ffffff26;backdrop-filter:blur(10px);-webkit-backdrop-filter:blur(10px);transition:background .25s,transform .25s,opacity .25s;opacity:0}
.hero-carousel:hover .hero-arrow{opacity:1}
@media(hover:none){.hero-arrow{opacity:.8}}
.hero-arrow:hover{background:#000000d9;transform:translateY(-50%) scale(1.1);border-color:#ffffff55}
.hero-arrow.prev{left:max(16px,calc(var(--pad) / 2))}
.hero-arrow.next{right:max(16px,calc(var(--pad) / 2))}
.hero-arrow svg{width:26px;height:26px}

.hero-dots{position:absolute;right:var(--pad);bottom:clamp(24px,5vh,44px);z-index:12;display:flex;align-items:center;gap:8px}
.hero-dot{height:5px;width:16px;border-radius:3px;background:#ffffff40;cursor:pointer;transition:all .35s var(--ease);border:0;padding:0}
.hero-dot.on{background:var(--accent);width:34px}
.hero-dot:hover{background:#ffffffaa}

/* ---------- rows & cards ---------- */
#rows{position:relative;z-index:3;margin-top:-64px}
.row{position:relative;margin-bottom:8px}
.row.pre{opacity:0;transform:translateY(28px)}
.row{transition:opacity .7s var(--ease),transform .7s var(--ease)}
.row.in{opacity:1;transform:none}
.row h2{font-size:clamp(18px,1.7vw,22px);font-weight:700;letter-spacing:-.015em;padding:0 var(--pad);display:flex;align-items:center;gap:10px}
.track{display:flex;gap:14px;overflow-x:auto;padding:16px var(--pad) 32px;scroll-snap-type:x proximity;scroll-padding:0 var(--pad);scrollbar-width:none;-webkit-overflow-scrolling:touch}
.track::-webkit-scrollbar{display:none}
.arrow{position:absolute;top:44px;bottom:32px;width:var(--pad);min-width:44px;z-index:8;display:grid;place-items:center;opacity:0;transition:opacity .25s,background .25s;color:#fff}
.arrow.l{left:0;background:linear-gradient(90deg,#0c0c0fe6,#0c0c0f00)}.arrow.r{right:0;background:linear-gradient(270deg,#0c0c0fe6,#0c0c0f00)}
.arrow svg{width:30px;height:30px;transition:transform .2s}.arrow:hover svg{transform:scale(1.25)}
@media(hover:hover){.row:hover .arrow.on{opacity:1}}
.arrow:not(.on){pointer-events:none}

.card{position:relative;flex:0 0 clamp(230px,21vw,330px);scroll-snap-align:start;cursor:pointer;transition:transform .45s var(--ease),opacity .35s;-webkit-tap-highlight-color:transparent}
.grid .card{flex:none}
@media(hover:hover){
  .card:hover{transform:scale(1.06);z-index:6}
  .track:has(.card:hover) .card:not(:hover),.grid:has(.card:hover) .card:not(:hover){opacity:.55}
}
.thumb{position:relative;aspect-ratio:16/9;border-radius:10px;overflow:hidden;background:var(--panel);box-shadow:0 8px 22px #0006;transition:box-shadow .45s}
.card:hover .thumb{box-shadow:0 22px 46px #000c,0 0 0 1px #ffffff30}
.thumb img{width:100%;height:100%;object-fit:cover;opacity:0;transition:opacity .5s,transform .7s var(--ease)}
.thumb img.ld{opacity:1}
.card:hover .thumb img{transform:scale(1.06)}
.play{position:absolute;inset:0;display:grid;place-items:center;background:linear-gradient(0deg,#000000b3,#0000 62%);opacity:0;transition:opacity .3s}
.play b{width:54px;height:54px;border-radius:50%;background:#fffffff2;color:#000;display:grid;place-items:center;transform:scale(.7);transition:transform .4s var(--ease)}
.card:hover .play{opacity:1}.card:hover .play b{transform:none}
.tag{position:absolute;top:9px;left:9px;font-size:11px;font-weight:800;letter-spacing:.04em;padding:2.5px 7px;border-radius:4px;background:#000000a6;backdrop-filter:blur(6px);-webkit-backdrop-filter:blur(6px)}
.tag.k{background:var(--accent);color:#1a0b00}
.tag.series-tag{background:var(--series);color:#fff}
.tag.anime-tag{background:#e11d48;color:#fff}
.tag.animemovie-tag{background:#d946ef;color:#fff}
.dur{position:absolute;right:9px;bottom:10px;font-size:11.5px;font-weight:600;padding:1.5px 6.5px;border-radius:4px;background:#000000b3}
.pbar{position:absolute;left:0;right:0;bottom:0;height:4px;background:#ffffff38}.pbar i{display:block;height:100%;background:var(--accent)}
.act{position:absolute;top:8px;right:8px;display:flex;gap:6px;opacity:0;transition:opacity .25s}
.card:hover .act,.card:focus-within .act{opacity:1}
@media(hover:none){.act{opacity:1}}
.act button{width:32px;height:32px;border-radius:50%;background:#000000b3;display:grid;place-items:center;backdrop-filter:blur(8px);transition:background .2s,transform .2s}
.act button:hover{background:#000;transform:scale(1.1)}.act svg{width:16px;height:16px}
.ct{margin-top:11px;font-weight:600;font-size:15px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.cm{display:flex;gap:12px;font-size:13px;color:var(--muted);margin-top:1px;white-space:nowrap;overflow:hidden;min-height:1.45em}

/* ---------- sections (Movies / Web Series / All) ---------- */
.sec{padding:90px var(--pad) 50px;min-height:80vh}
.sec-h{display:flex;flex-wrap:wrap;align-items:center;gap:14px 24px;margin-bottom:26px}
.sec-h h2{font-size:clamp(22px,2.4vw,28px);font-weight:800;letter-spacing:-.02em;margin-right:auto}
.chips{display:flex;gap:8px;overflow-x:auto;scrollbar-width:none;max-width:100%}.chips::-webkit-scrollbar{display:none}
.chip{padding:7px 16px;border-radius:999px;border:1px solid var(--line);color:var(--muted);font-size:13.5px;font-weight:600;white-space:nowrap;transition:all .25s var(--ease)}
.chip:hover{color:#fff;border-color:#ffffff4d}.chip.on{background:#fff;color:#000;border-color:#fff}
.sort{padding:7px 14px;border:1px solid var(--line);border-radius:8px;color:var(--muted);font-size:13.5px;font-weight:600;background:var(--panel);appearance:none;-webkit-appearance:none}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(clamp(220px,21vw,310px),1fr));gap:32px 14px}
.empty{padding:90px 20px;text-align:center;color:var(--muted)}
.empty h3{color:var(--text);font-size:22px;margin-bottom:8px}

/* ---------- detail modals (Netflix Style) ---------- */
.detail-modal{position:fixed;inset:0;z-index:85;display:flex;justify-content:center;padding:clamp(16px,3vh,44px) var(--pad);background:#000000cc;backdrop-filter:blur(16px);-webkit-backdrop-filter:blur(16px);overflow-y:auto;opacity:0;pointer-events:none;transition:opacity .3s}
.detail-modal.open{opacity:1;pointer-events:auto}
.detail-wrap{position:relative;width:min(920px,100%);background:var(--panel);border:1px solid var(--line);border-radius:18px;overflow:hidden;box-shadow:0 30px 80px #000000fa;transform:translateY(24px) scale(.98);transition:transform .35s var(--ease);margin:auto 0}
.detail-modal.open .detail-wrap{transform:none}
.modal-close-btn{position:absolute;top:16px;right:16px;z-index:10;width:40px;height:40px;border-radius:50%;background:#000000a6;color:#fff;font-size:26px;line-height:1;display:grid;place-items:center;border:1px solid #ffffff26;cursor:pointer;backdrop-filter:blur(8px);transition:background .2s,transform .2s}
.modal-close-btn:hover{background:#fff;color:#000;transform:scale(1.08)}
.detail-hero{position:relative;min-height:340px;overflow:hidden;display:flex;align-items:flex-end;background:#0c0c0f}
.detail-bg{position:absolute;inset:0;width:100%;height:100%;object-fit:cover;opacity:0;filter:blur(2px);transform:scale(1.04);transition:opacity .6s}
.detail-bg.ld{opacity:.45}
.detail-hero::before{content:"";position:absolute;inset:0;z-index:1;background:linear-gradient(0deg,#16161a 0%,#16161af2 35%,#16161a99 75%,#16161ad9 100%),linear-gradient(90deg,#16161af5 0%,#16161a99 50%,#16161a55 100%)}
.detail-hero-content{position:relative;z-index:2;padding:28px 32px;width:100%}
.detail-hero-layout{display:flex;align-items:flex-end;gap:26px}
.detail-poster-card{position:relative;width:clamp(160px,20vw,230px);aspect-ratio:16/9;border-radius:12px;overflow:hidden;flex:none;background:#0c0c0f;box-shadow:0 14px 34px #000c,0 0 0 1px #ffffff26;cursor:pointer;transition:transform .25s,box-shadow .25s}
.detail-poster-card:hover{transform:scale(1.04);box-shadow:0 20px 44px #000f,0 0 0 2px var(--accent)}
.detail-poster-card img{width:100%;height:100%;object-fit:cover;opacity:0;transition:opacity .4s}
.detail-poster-card img.ld{opacity:1}
.poster-play-glow{position:absolute;inset:0;display:grid;place-items:center;background:#00000059;opacity:0;transition:opacity .2s}
.detail-poster-card:hover .poster-play-glow{opacity:1}
.poster-play-glow svg{width:46px;height:46px;fill:#fff;filter:drop-shadow(0 4px 14px #000)}
.detail-meta-block{flex:1;min-width:0}
.detail-badge-row{display:flex;align-items:center;gap:8px;margin-bottom:8px}
.detail-badge{display:inline-block;font-size:11px;font-weight:800;letter-spacing:.08em;padding:3px 9px;border-radius:4px;background:var(--accent);color:#000}
.detail-badge.series-badge{background:var(--series);color:#fff}
.detail-quality-pill{font-size:11px;font-weight:700;padding:2px 8px;border-radius:4px;border:1px solid #ffffff40;color:#ffffffcc}
.detail-title{font-size:clamp(24px,4.5vw,44px);font-weight:800;letter-spacing:-.025em;line-height:1.15;margin-bottom:8px;text-shadow:0 2px 14px #000b}
.detail-meta-line{display:flex;flex-wrap:wrap;align-items:center;gap:12px;font-size:14px;color:#ffffffb3;font-weight:500;margin-bottom:18px}
.detail-meta-line .pill{padding:1.5px 8px;border:1px solid #ffffff4d;border-radius:4px;font-size:12px;font-weight:700;color:#fff}
.detail-actions{display:flex;flex-wrap:wrap;gap:10px}
@media(max-width:680px){
  .detail-hero-layout{flex-direction:column;align-items:flex-start;gap:16px}
  .detail-poster-card{width:min(200px,65vw)}
  .detail-hero-content{padding:20px}
}
.detail-body{padding:24px 32px 36px}
.detail-specs-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(210px,1fr));gap:14px;margin-bottom:28px}
.spec-card{background:#ffffff08;border:1px solid #ffffff10;border-radius:10px;padding:12px 14px}
.spec-title{font-size:11px;text-transform:uppercase;font-weight:700;color:var(--muted);letter-spacing:.06em;margin-bottom:6px}
.spec-val{font-size:13.5px;color:#f0f0f4;line-height:1.4;word-break:break-all}
.audio-list{display:flex;flex-wrap:wrap;gap:6px}
.audio-chip{font-size:12px;font-weight:600;padding:2.5px 8px;border-radius:4px;background:#ffffff1a;color:#fff}
.related-sec{margin-top:24px}
.related-sec h3{font-size:18px;font-weight:700;margin-bottom:14px}

/* Series Hub Season & Episodes */
.series-nav-header{display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:12px;border-bottom:1px solid var(--line);padding-bottom:12px;margin-bottom:18px}
.series-nav-header h2{font-size:20px;font-weight:700}
.season-tabs{display:flex;gap:8px;overflow-x:auto;scrollbar-width:none;max-width:100%}
.season-tab{padding:6px 16px;border-radius:999px;border:1px solid var(--line);color:var(--muted);font-size:13px;font-weight:600;cursor:pointer;white-space:nowrap;transition:all .2s}
.season-tab:hover{color:#fff;border-color:#ffffff4d}
.season-tab.on{background:#fff;color:#000;border-color:#fff}
.episodes-list{display:flex;flex-direction:column;gap:8px}
.ep-row{display:flex;align-items:center;gap:16px;padding:12px 14px;border-radius:10px;cursor:pointer;transition:background .2s;border:1px solid transparent}
.ep-row:hover{background:#ffffff0f;border-color:#ffffff17}
.ep-num{font-size:18px;font-weight:700;color:var(--muted);width:26px;text-align:center;flex:none}
.ep-thumb-wrap{position:relative;width:130px;aspect-ratio:16/9;border-radius:6px;overflow:hidden;background:#0c0c0f;flex:none;box-shadow:0 4px 12px #0006}
.ep-thumb{width:100%;height:100%;object-fit:cover;opacity:0;transition:opacity .4s}
.ep-thumb.ld{opacity:1}
.ep-play-overlay{position:absolute;inset:0;display:grid;place-items:center;background:#00000066;opacity:0;transition:opacity .2s}
.ep-row:hover .ep-play-overlay{opacity:1}
.ep-play-overlay svg{width:24px;height:24px;fill:#fff}
.ep-details{flex:1;min-width:0}
.ep-header-line{display:flex;align-items:center;justify-content:space-between;gap:10px;margin-bottom:4px}
.ep-name{font-size:15px;font-weight:600;color:#fff;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.ep-dur{font-size:13px;color:var(--muted);font-weight:600;flex:none}
.ep-sub{font-size:12.5px;color:var(--muted);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.ep-copy-btn{width:34px;height:34px;border-radius:50%;display:grid;place-items:center;color:var(--muted);transition:all .2s;background:#ffffff0a}
.ep-copy-btn:hover{color:#fff;background:#ffffff26;transform:scale(1.1)}

/* Search results */
#results{padding:96px var(--pad) 60px;min-height:80vh}
#results h2{font-size:18px;font-weight:600;color:var(--muted);margin-bottom:24px}
#results h2 b{color:var(--text)}
body.searching #hero,body.searching #rows,body.searching #secMovies,body.searching #secSeries,body.searching #secAnimeSeries,body.searching #secAnimeMovies{display:none}
body:not(.searching) #results{display:none}

/* Skeleton & Footer */
.skel{background:linear-gradient(100deg,#16161a 30%,#202027 48%,#16161a 66%);background-size:300% 100%;animation:sh 1.5s linear infinite}
@keyframes sh{to{background-position:-300% 0}}
.hero.is-skel .hero-c{display:none}
.sk-row{padding:0 var(--pad);display:flex;gap:12px;overflow:hidden;margin-bottom:34px}
.sk-row div{flex:0 0 clamp(230px,21vw,340px);aspect-ratio:16/9;border-radius:10px}
footer{padding:10px var(--pad) 50px;color:#6c6c76;font-size:13px;display:flex;flex-wrap:wrap;gap:6px 18px}
footer .live{color:var(--accent)}

/* QR Modal & Toast */
.modal{position:fixed;inset:0;z-index:90;display:grid;place-items:center;padding:20px;background:#000000b8;backdrop-filter:blur(10px);-webkit-backdrop-filter:blur(10px);opacity:0;pointer-events:none;transition:opacity .3s}
.modal.open{opacity:1;pointer-events:auto}
.box{width:min(380px,100%);background:#1a1a1f;border:1px solid var(--line);border-radius:18px;padding:28px;text-align:center;transform:translateY(20px) scale(.97);transition:transform .45s var(--ease)}
.modal.open .box{transform:none}
.box h3{font-size:20px;margin-bottom:6px}.box p{color:var(--muted);font-size:14px;margin-bottom:18px}
.box img{width:210px;height:210px;background:#fff;border-radius:12px;padding:8px;margin-bottom:14px}
.box .url{color:#fff;font-weight:600;word-break:break-all;margin-bottom:18px;font-size:15px}
.box .btn{width:100%;justify-content:center;padding:11px}
.toast{position:fixed;left:50%;bottom:calc(28px + env(safe-area-inset-bottom));z-index:100;background:#fff;color:#000;font-weight:600;font-size:14px;padding:11px 20px;border-radius:999px;box-shadow:0 12px 30px #0009;transform:translate(-50%,90px);opacity:0;transition:transform .45s var(--ease),opacity .3s;pointer-events:none}
.toast.show{transform:translate(-50%,0);opacity:1}

@media(max-width:768px){
  .nav{gap:14px}.nav-links{gap:12px}.nav .lnk{font-size:13.5px}
  .hero{height:72vh;min-height:420px}.hero-c{padding-bottom:80px}
  .btn{padding:10px 20px;font-size:14.5px}
  .detail-hero{max-height:280px}
  .detail-body{padding:18px 20px 28px}
  .hero-arrow{display:none}
  .hero-dots{bottom:18px;right:18px}
}
@media(prefers-reduced-motion:reduce){
  *,*::before,*::after{animation-duration:.01ms!important;animation-iteration-count:1!important;transition-duration:.01ms!important;scroll-behavior:auto!important}
}
</style>
</head>
<body>

<header class="nav" id="nav">
  <a class="logo" href="/" aria-label="__APP__ home"><svg class="i f" viewBox="0 0 24 24" style="width:22px;height:22px;color:var(--accent)"><polygon points="6 4 20 12 6 20"/></svg><span>__APP__</span></a>
  <nav class="nav-links">
    <a class="lnk on" href="#" id="lnkHome">Home</a>
    <a class="lnk" href="#anime-series" id="lnkAnimeSeries">Anime Series</a>
    <a class="lnk" href="#series" id="lnkSeries">Web Series</a>
    <a class="lnk" href="#anime-movies" id="lnkAnimeMovies">Anime Movies</a>
    <a class="lnk" href="#movies" id="lnkMovies">Movies</a>
  </nav>
  <div class="grow"></div>
  <div class="search" id="search">
    <button class="ib" id="searchBtn" aria-label="Search"><svg class="i" viewBox="0 0 24 24"><circle cx="11" cy="11" r="7"/><path d="M21 21l-4.3-4.3"/></svg></button>
    <input id="q" type="search" placeholder="Movies, web series, episodes..." autocomplete="off" spellcheck="false" aria-label="Search titles">
  </div>
  <button class="ib" id="connectBtn" aria-label="Open on another device" title="Open on another device"><svg class="i" viewBox="0 0 24 24"><rect x="3" y="3" width="7" height="7" rx="1"/><rect x="14" y="3" width="7" height="7" rx="1"/><rect x="3" y="14" width="7" height="7" rx="1"/><path d="M14 14h3v3h-3zM20 14v.01M14 20v.01M20 20h1v1h-1z"/></svg></button>
</header>

<main>
  <!-- HERO BANNER -->
  <section class="hero is-skel skel" id="hero"></section>

  <!-- HOME VIEW ROWS -->
  <div id="rows"><div class="sk-row"><div class="skel"></div><div class="skel"></div><div class="skel"></div><div class="skel"></div></div></div>

  <!-- ANIME WEB SERIES CATALOG VIEW -->
  <section class="sec" id="secAnimeSeries" hidden>
    <div class="sec-h">
      <h2>Anime Web Series</h2>
      <div class="chips" id="animeSeriesChips"></div>
      <select class="sort" id="animeSeriesSort" aria-label="Sort anime series">
        <option value="az">A to Z</option><option value="eps">Most Episodes</option>
        <option value="seasons">Most Seasons</option><option value="new">Recently Added</option>
        <option value="big">Largest Size</option>
      </select>
    </div>
    <div class="grid" id="animeSeriesGrid"></div>
  </section>

  <!-- WEB SERIES CATALOG VIEW -->
  <section class="sec" id="secSeries" hidden>
    <div class="sec-h">
      <h2>Web Series & TV Shows</h2>
      <div class="chips" id="seriesChips"></div>
      <select class="sort" id="seriesSort" aria-label="Sort series">
        <option value="az">A to Z</option><option value="eps">Most Episodes</option>
        <option value="seasons">Most Seasons</option><option value="new">Recently Added</option>
        <option value="big">Largest Size</option>
      </select>
    </div>
    <div class="grid" id="seriesGrid"></div>
  </section>

  <!-- ANIME MOVIES CATALOG VIEW -->
  <section class="sec" id="secAnimeMovies" hidden>
    <div class="sec-h">
      <h2>Anime Movies</h2>
      <div class="chips" id="animeMovieChips"></div>
      <select class="sort" id="animeMovieSort" aria-label="Sort anime movies">
        <option value="az">A to Z</option><option value="new">Recently Added</option>
        <option value="long">Longest</option><option value="big">Largest File</option>
      </select>
    </div>
    <div class="grid" id="animeMovieGrid"></div>
  </section>

  <!-- MOVIES CATALOG VIEW -->
  <section class="sec" id="secMovies" hidden>
    <div class="sec-h">
      <h2>Blockbuster Movies</h2>
      <div class="chips" id="movieChips"></div>
      <select class="sort" id="movieSort" aria-label="Sort movies">
        <option value="az">A to Z</option><option value="new">Recently Added</option>
        <option value="long">Longest</option><option value="big">Largest File</option>
      </select>
    </div>
    <div class="grid" id="movieGrid"></div>
  </section>

  <!-- SEARCH RESULTS -->
  <section id="results"><h2 id="resH"></h2><div class="grid" id="resGrid"></div></section>
</main>
<footer id="foot"></footer>

<!-- NETFLIX MOVIE DETAIL MODAL -->
<div class="detail-modal" id="movieModal" aria-hidden="true">
  <div class="detail-wrap" role="dialog" aria-label="Movie details">
    <button class="modal-close-btn" id="movieModalClose" aria-label="Close">&times;</button>
    <div class="detail-hero">
      <img class="detail-bg" id="movieModalBg" alt="" onload="this.classList.add('ld')">
      <div class="detail-hero-content">
        <div class="detail-hero-layout">
          <div class="detail-poster-card" id="movieModalPosterCard" title="Click to play movie">
            <img id="movieModalPoster" alt="" onload="this.classList.add('ld')">
            <div class="poster-play-glow"><svg class="i f" viewBox="0 0 24 24"><polygon points="6 4 20 12 6 20"/></svg></div>
          </div>
          <div class="detail-meta-block">
            <div class="detail-badge-row">
              <span class="detail-badge" id="movieModalBadge">MOVIE</span>
              <span class="detail-quality-pill" id="movieModalQualityBadge">1080p</span>
            </div>
            <h1 class="detail-title" id="movieModalTitle"></h1>
            <div class="detail-meta-line" id="movieModalMeta"></div>
            <div class="detail-actions">
              <a class="btn pri" id="movieModalPlay" href="#"><svg class="i f" viewBox="0 0 24 24"><polygon points="6 4 20 12 6 20"/></svg>Play Movie</a>
              <a class="btn ghost" id="movieModalResume" href="#" hidden>Resume</a>
              <button class="btn ghost" id="movieModalCopy"><svg class="i" viewBox="0 0 24 24"><path d="M10 13a5 5 0 0 0 7.5.5l3-3a5 5 0 0 0-7-7l-1.7 1.7"/><path d="M14 11a5 5 0 0 0-7.5-.5l-3 3a5 5 0 0 0 7 7l1.7-1.7"/></svg>Copy Stream Link</button>
            </div>
          </div>
        </div>
      </div>
    </div>
    <div class="detail-body">
      <div class="detail-specs-grid">
        <div class="spec-card">
          <div class="spec-title">Audio Tracks</div>
          <div class="audio-list" id="movieModalAudio"></div>
        </div>
        <div class="spec-card">
          <div class="spec-title">Video Quality & Codec</div>
          <div class="spec-val" id="movieModalQuality"></div>
        </div>
        <div class="spec-card">
          <div class="spec-title">File Details</div>
          <div class="spec-val" id="movieModalFile"></div>
        </div>
      </div>
      <div class="related-sec" id="movieRelatedSec">
        <h3>More Like This</h3>
        <div class="track" id="movieRelatedTrack"></div>
      </div>
    </div>
  </div>
</div>

<!-- NETFLIX WEB SERIES DETAIL MODAL -->
<div class="detail-modal" id="seriesModal" aria-hidden="true">
  <div class="detail-wrap" role="dialog" aria-label="Web Series details">
    <button class="modal-close-btn" id="seriesModalClose" aria-label="Close">&times;</button>
    <div class="detail-hero">
      <img class="detail-bg" id="seriesModalBg" alt="" onload="this.classList.add('ld')">
      <div class="detail-hero-content">
        <div class="detail-hero-layout">
          <div class="detail-poster-card" id="seriesModalPosterCard" title="Click to play series">
            <img id="seriesModalPoster" alt="" onload="this.classList.add('ld')">
            <div class="poster-play-glow"><svg class="i f" viewBox="0 0 24 24"><polygon points="6 4 20 12 6 20"/></svg></div>
          </div>
          <div class="detail-meta-block">
            <div class="detail-badge-row">
              <span class="detail-badge series-badge" id="seriesModalBadge">SERIES</span>
              <span class="detail-quality-pill" id="seriesModalQualityBadge">1080p</span>
            </div>
            <h1 class="detail-title" id="seriesModalTitle"></h1>
            <div class="detail-meta-line" id="seriesModalMeta"></div>
            <div class="detail-actions">
              <a class="btn pri" id="seriesModalPlay" href="#"><svg class="i f" viewBox="0 0 24 24"><polygon points="6 4 20 12 6 20"/></svg>Play S1 E1</a>
              <button class="btn ghost" id="seriesModalCopy"><svg class="i" viewBox="0 0 24 24"><path d="M10 13a5 5 0 0 0 7.5.5l3-3a5 5 0 0 0-7-7l-1.7 1.7"/><path d="M14 11a5 5 0 0 0-7.5-.5l-3 3a5 5 0 0 0 7 7l1.7-1.7"/></svg>Copy Stream Link</button>
            </div>
          </div>
        </div>
      </div>
    </div>
    <div class="detail-body">
      <div class="series-nav-header">
        <h2>Episodes</h2>
        <div class="season-tabs" id="seasonTabs"></div>
      </div>
      <div class="episodes-list" id="episodesList"></div>
    </div>
  </div>
</div>

<div class="modal" id="qr" aria-hidden="true">
  <div class="box" role="dialog" aria-label="Open on another device">
    <h3>Watch on your iPad or phone</h3>
    <p>Join the same Wi-Fi, then scan this code.</p>
    <img id="qrImg" alt="QR code" width="210" height="210" onerror="this.style.display='none'">
    <div class="url" id="qrUrl"></div>
    <button class="btn ghost" id="qrClose">Close</button>
  </div>
</div>
<div class="toast" id="toast" role="status"></div>

<script>
(() => {
"use strict";
const $ = s => document.querySelector(s);
const esc = s => String(s || "").replace(/[&<>"']/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const encPath = p => p.split("/").map(encodeURIComponent).join("/");
const dur = s => { s = Math.round(s || 0); if (s <= 0) return ""; const h = Math.floor(s / 3600), m = Math.floor(s % 3600 / 60); return h ? `${h}h ${m}m` : `${Math.max(m,1)}m`; };
const gb = b => (b / 1073741824).toFixed(b > 1e11 ? 0 : 1);
const IC = {
  play:'<polygon points="6 4 20 12 6 20" fill="currentColor" stroke="none"/>',
  info:'<circle cx="12" cy="12" r="9"/><path d="M12 11v5M12 8v.01"/>',
  shuffle:'<path d="M16 3h5v5M4 20 21 3M21 16v5h-5M15 15l6 6M4 4l5 5"/>',
  link:'<path d="M10 13a5 5 0 0 0 7.5.5l3-3a5 5 0 0 0-7-7l-1.7 1.7"/><path d="M14 11a5 5 0 0 0-7.5-.5l-3 3a5 5 0 0 0 7 7l1.7-1.7"/>',
  x:'<path d="M18 6 6 18M6 6l12 12"/>',
  left:'<path d="m15 18-6-6 6-6"/>', right:'<path d="m9 18 6-6-6-6"/>'
};
const ic = (n, cls = "") => `<svg class="i ${cls}" viewBox="0 0 24 24">${IC[n]}</svg>`;

let data = { movies: [], anime_movies: [], anime_series: [], web_series: [], all_series: [], all_movies: [], all_items: [] }, sig = "", first = true;
let currentTab = "home";
let movieFilter = "all", movieSort = "az";
let animeMovieFilter = "all", animeMovieSort = "az";
let seriesFilter = "all", seriesSort = "az";
let animeSeriesFilter = "all", animeSeriesSort = "az";
let query = "", activeSeries = null, activeSeasonId = "";

const href = m => "/player/" + encPath(m.path);

/* ---------- data fetch ---------- */
let loadT;
async function load() {
  clearTimeout(loadT);
  let busy = false;
  try {
    const r = await fetch("/api/library", { cache: "no-store" });
    data = await r.json();
    const as = data.anime_series || [], ws = data.web_series || [], am = data.anime_movies || [], m = data.movies || [];
    const s = JSON.stringify({ as: as.length, ws: ws.length, am: am.length, m: m.length, t: data.total_size });
    if (s !== sig) { sig = s; render(); }
    foot();
    busy = data.scanning;
  } catch (e) { busy = true; }
  loadT = setTimeout(load, busy ? 1200 : 20000);
}

/* ---------- card HTML generators ---------- */
function movieCard(m, i, o = {}) {
  const p = m.progress, pct = p && p.dur ? Math.min(100, p.pos / p.dur * 100) : 0;
  const left = p && p.dur ? Math.max(1, Math.round((p.dur - p.pos) / 60)) : 0;
  const sub = (o.resume && left ? [`${left} min left`] : [m.year, dur(m.duration), m.quality]).filter(Boolean).map(x => `<span>${esc(x)}</span>`).join("");
  const act = (o.clear ? `<button data-clear="${esc(m.path)}" title="Remove from Continue watching" aria-label="Remove">${ic("x")}</button>` : "")
            + `<button data-copy="${esc(m.path)}" title="Copy stream link" aria-label="Copy stream link">${ic("link")}</button>`;
  const playOverlay = o.resume
    ? `<div class="play" title="Resume movie"><b>${ic("play")}</b></div>`
    : `<div class="play" title="View movie details"><b>${ic("info")}</b></div>`;
  const resumeAttr = o.resume ? ' data-resume="1"' : '';
  const isAnime = m.category === "anime_movies";
  const tagHtml = m.quality === "4K" ? '<span class="tag k">4K</span>' : (isAnime ? '<span class="tag animemovie-tag">ANIME MOVIE</span>' : '<span class="tag">MOVIE</span>');
  return `<article class="card" data-type="movie" data-p="${esc(m.path)}"${resumeAttr} tabindex="0" role="link" aria-label="${o.resume ? 'Resume' : 'Open'} ${esc(m.title)}">
    <div class="thumb"><img src="/thumb/${encPath(m.path)}?v=${m.mtime}" loading="lazy" decoding="async" alt="" onload="this.classList.add('ld')">
      ${playOverlay}
      ${tagHtml}
      ${m.duration ? `<span class="dur">${dur(m.duration)}</span>` : ""}
      ${pct ? `<div class="pbar"><i style="width:${pct}%"></i></div>` : ""}
      <div class="act">${act}</div></div>
    <div class="ct">${esc(m.title)}</div><div class="cm">${sub}</div></article>`;
}

function seriesCard(s, i, o = {}) {
  const countStr = s.seasonsCount > 1 ? `${s.seasonsCount} Seasons` : `${s.totalEpisodes} Episodes`;
  const sub = [countStr, s.quality, gb(s.totalSize) + " GB"].filter(Boolean).map(x => `<span>${esc(x)}</span>`).join("");
  const firstEp = (s.seasons[0] && s.seasons[0].episodes[0]) ? s.seasons[0].episodes[0].path : s.posterPath;
  const act = `<button data-copy="${esc(firstEp)}" title="Copy stream link" aria-label="Copy stream link">${ic("link")}</button>`;
  const isAnime = s.category === "anime_series";
  const tagHtml = isAnime ? '<span class="tag anime-tag">ANIME</span>' : '<span class="tag series-tag">SERIES</span>';
  return `<article class="card" data-type="series" data-series-id="${esc(s.id)}" tabindex="0" role="link" aria-label="Open ${esc(s.title)}">
    <div class="thumb"><img src="/thumb/${encPath(s.posterPath)}?v=${s.added}" loading="lazy" decoding="async" alt="" onload="this.classList.add('ld')">
      <div class="play" title="View episodes and details"><b>${ic("info")}</b></div>
      ${tagHtml}
      <span class="dur">${countStr}</span>
      <div class="act">${act}</div></div>
    <div class="ct">${esc(s.title)}</div><div class="cm">${sub}</div></article>`;
}

function rowHTML(id, title, list, cardFn, o = {}) {
  if (!list || !list.length) return "";
  return `<section class="row ${first ? "pre" : "in"}" data-row="${id}"><h2>${esc(title)}</h2>
    <button class="arrow l" aria-label="Scroll left">${ic("left")}</button>
    <div class="track" data-track="${id}">${list.map((it, i) => cardFn(it, i, o)).join("")}</div>
    <button class="arrow r on" aria-label="Scroll right">${ic("right")}</button></section>`;
}

const sorters = {
  az: (a, b) => a.title.localeCompare(b.title, undefined, { numeric: true }),
  new: (a, b) => (b.added || 0) - (a.added || 0),
  long: (a, b) => (b.duration || 0) - (a.duration || 0),
  big: (a, b) => (b.size || b.totalSize || 0) - (a.size || a.totalSize || 0),
  eps: (a, b) => (b.totalEpisodes || 0) - (a.totalEpisodes || 0),
  seasons: (a, b) => (b.seasonsCount || 0) - (a.seasonsCount || 0),
};

/* ---------- hero carousel ---------- */
let heroItems = [];
let heroCurrentIdx = 0;
let heroTimer = null;
let heroScrollDebounce = null;
let heroItem = null;

let wrapTimer = null;

function jumpInstant(track, leftPos) {
  track.style.scrollBehavior = "auto";
  track.style.scrollSnapType = "none";
  track.scrollLeft = leftPos;
  void track.offsetWidth;
  track.style.scrollBehavior = "";
  track.style.scrollSnapType = "";
}

function heroSlideHTML(it, idx, isClone = false) {
  const isSeries = !!(it.seasonsCount);
  let why = isSeries ? (it.category === "anime_series" ? "Featured Anime Series" : "Featured Web Series") : (it.category === "anime_movies" ? "Featured Anime Movie" : "Featured Blockbuster Movie");
  const q = it.quality ? `<span class="q">${esc(it.quality)}</span>` : "";
  const metaLine = isSeries ? `<span>${it.seasonsCount} ${it.seasonsCount > 1 ? "Seasons" : "Season"}</span><span>${it.totalEpisodes} Episodes</span>` : `<span>${it.year || ""}</span><span>${dur(it.duration)}</span>`;
  const poster = isSeries ? it.posterPath : it.path;
  const playTarget = isSeries ? ((it.latestProgress && it.latestProgress.path) || (it.seasons[0] && it.seasons[0].episodes[0] && it.seasons[0].episodes[0].path) || it.posterPath) : it.path;

  return `<div class="hero-slide ${idx === 0 && !isClone ? "active" : ""}" data-idx="${idx}" ${isClone ? 'data-clone="1"' : ''} data-type="${isSeries ? 'series' : 'movie'}" data-id="${esc(isSeries ? it.id : it.path)}">
    <img class="bg" src="/thumb/${encPath(poster)}?w=1280&v=${it.mtime || it.added}" alt="" onload="this.classList.add('ld')">
    <div class="hero-c">
      <div class="why">${why}</div>
      <h1>${esc(it.title)}</h1>
      <div class="facts">${metaLine}${q}</div>
      <div class="btns">
        <button class="btn pri hero-btn-play" data-target="${esc(playTarget)}">${ic("play")}Watch Now</button>
        <button class="btn ghost hero-btn-info" data-type="${isSeries ? 'series' : 'movie'}" data-id="${esc(isSeries ? it.id : it.path)}">${ic("info")}${isSeries ? "Explore Episodes" : "Movie Details"}</button>
        <button class="btn ghost hero-btn-surprise">${ic("shuffle")}Surprise me</button>
      </div>
    </div>
  </div>`;
}

function heroCarouselHTML(items) {
  if (!items || !items.length) return "";
  let slides = "";
  if (items.length > 1) {
    // Clone of last item prepended
    slides += heroSlideHTML(items[items.length - 1], items.length - 1, true);
    // Real items
    slides += items.map((it, i) => heroSlideHTML(it, i, false)).join("");
    // Clone of first item appended
    slides += heroSlideHTML(items[0], 0, true);
  } else {
    slides = heroSlideHTML(items[0], 0, false);
  }

  const dots = items.length > 1 ? `<div class="hero-dots" id="heroDots">${items.map((_, i) => `<button class="hero-dot ${i === 0 ? "on" : ""}" data-idx="${i}" aria-label="Slide ${i + 1}"></button>`).join("")}</div>` : "";
  const arrows = items.length > 1 ? `
    <button class="hero-arrow prev" id="heroPrev" aria-label="Previous slide">${ic("left")}</button>
    <button class="hero-arrow next" id="heroNext" aria-label="Next slide">${ic("right")}</button>` : "";
  return `<div class="hero-carousel" id="heroCarousel">
    <div class="hero-track" id="heroTrack">${slides}</div>
    ${arrows}
    ${dots}
  </div>`;
}

function stepHero(delta) {
  const track = $("#heroTrack");
  if (!track || !heroItems.length) return;
  const N = heroItems.length;
  if (N <= 1) return;

  const slides = track.querySelectorAll(".hero-slide");
  clearTimeout(wrapTimer);

  if (delta > 0) {
    if (heroCurrentIdx < N - 1) {
      heroCurrentIdx++;
      const target = slides[heroCurrentIdx + 1];
      if (target) track.scrollTo({ left: target.offsetLeft, behavior: "smooth" });
    } else {
      // At last slide -> smoothly glide forward to clone of first slide (index N + 1)
      heroCurrentIdx = 0;
      const target = slides[N + 1];
      if (target) track.scrollTo({ left: target.offsetLeft, behavior: "smooth" });
      wrapTimer = setTimeout(() => {
        jumpInstant(track, slides[1].offsetLeft);
      }, 500);
    }
  } else if (delta < 0) {
    if (heroCurrentIdx > 0) {
      heroCurrentIdx--;
      const target = slides[heroCurrentIdx + 1];
      if (target) track.scrollTo({ left: target.offsetLeft, behavior: "smooth" });
    } else {
      // At first slide -> smoothly glide backward to clone of last slide (index 0)
      heroCurrentIdx = N - 1;
      const target = slides[0];
      if (target) track.scrollTo({ left: target.offsetLeft, behavior: "smooth" });
      wrapTimer = setTimeout(() => {
        jumpInstant(track, slides[N].offsetLeft);
      }, 500);
    }
  }
  updateHeroActive();
}

function goToHeroSlide(idx) {
  const track = $("#heroTrack");
  if (!track || !heroItems.length) return;
  const N = heroItems.length;
  if (N <= 1) return;
  clearTimeout(wrapTimer);
  heroCurrentIdx = ((idx % N) + N) % N;
  const slides = track.querySelectorAll(".hero-slide");
  const target = slides[heroCurrentIdx + 1];
  if (target) track.scrollTo({ left: target.offsetLeft, behavior: "smooth" });
  updateHeroActive();
}

function updateHeroActive() {
  const slides = document.querySelectorAll(".hero-slide");
  slides.forEach(sl => {
    const isClone = sl.hasAttribute("data-clone");
    const slIdx = parseInt(sl.dataset.idx, 10);
    sl.classList.toggle("active", slIdx === heroCurrentIdx && !isClone);
  });
  document.querySelectorAll(".hero-dot").forEach((dot, i) => {
    dot.classList.toggle("on", i === heroCurrentIdx);
  });
}

function startHeroAuto() {
  stopHeroAuto();
  if (!heroItems || heroItems.length <= 1) return;
  heroTimer = setInterval(() => {
    if (document.hidden || currentTab !== "home") return;
    stepHero(1);
  }, 5500);
}

function stopHeroAuto() {
  if (heroTimer) {
    clearInterval(heroTimer);
    heroTimer = null;
  }
}

function bindHeroEvents() {
  const track = $("#heroTrack");
  const carousel = $("#heroCarousel");
  if (!track || !carousel) return;

  track.addEventListener("scroll", () => {
    clearTimeout(heroScrollDebounce);
    heroScrollDebounce = setTimeout(() => {
      const w = track.clientWidth;
      if (w <= 0) return;
      const slides = track.querySelectorAll(".hero-slide");
      const N = heroItems.length;
      if (N <= 1 || !slides.length) return;

      const elemIdx = Math.round(track.scrollLeft / w);
      if (elemIdx >= N + 1) {
        jumpInstant(track, slides[1].offsetLeft);
        heroCurrentIdx = 0;
      } else if (elemIdx <= 0) {
        jumpInstant(track, slides[N].offsetLeft);
        heroCurrentIdx = N - 1;
      } else {
        heroCurrentIdx = elemIdx - 1;
      }
      updateHeroActive();
    }, 60);
  }, { passive: true });

  carousel.addEventListener("mouseenter", stopHeroAuto);
  carousel.addEventListener("mouseleave", () => { if (currentTab === "home") startHeroAuto(); });
  carousel.addEventListener("touchstart", stopHeroAuto, { passive: true });
  carousel.addEventListener("touchend", () => { if (currentTab === "home") startHeroAuto(); }, { passive: true });

  const prevBtn = $("#heroPrev");
  if (prevBtn) {
    prevBtn.addEventListener("click", () => {
      stopHeroAuto();
      stepHero(-1);
      startHeroAuto();
    });
  }
  const nextBtn = $("#heroNext");
  if (nextBtn) {
    nextBtn.addEventListener("click", () => {
      stopHeroAuto();
      stepHero(1);
      startHeroAuto();
    });
  }

  const dots = $("#heroDots");
  if (dots) {
    dots.addEventListener("click", e => {
      const dot = e.target.closest(".hero-dot");
      if (dot) {
        stopHeroAuto();
        goToHeroSlide(parseInt(dot.dataset.idx, 10));
        startHeroAuto();
      }
    });
  }
}

/* ---------- rendering ---------- */
function render() {
  const hero = $("#hero"), rows = $("#rows");
  const animeSeries = data.anime_series || [];
  const webSeries = data.web_series || [];
  const animeMovies = data.anime_movies || [];
  const movies = data.movies || [];
  const allSeries = data.all_series || [...animeSeries, ...webSeries];
  const allMovies = data.all_movies || [...animeMovies, ...movies];
  const all = data.all_items || [];
  const scroll = {};
  document.querySelectorAll("[data-track]").forEach(t => scroll[t.dataset.track] = t.scrollLeft);

  // Update nav links active state
  document.querySelectorAll(".nav .lnk").forEach(l => l.classList.remove("on"));
  if (currentTab === "home") $("#lnkHome").classList.add("on");
  else if (currentTab === "anime_series") $("#lnkAnimeSeries").classList.add("on");
  else if (currentTab === "web_series") $("#lnkSeries").classList.add("on");
  else if (currentTab === "anime_movies") $("#lnkAnimeMovies").classList.add("on");
  else if (currentTab === "movies") $("#lnkMovies").classList.add("on");

  // Tab visibility toggles
  $("#secAnimeSeries").hidden = (currentTab !== "anime_series");
  $("#secSeries").hidden = (currentTab !== "web_series");
  $("#secAnimeMovies").hidden = (currentTab !== "anime_movies");
  $("#secMovies").hidden = (currentTab !== "movies");
  hero.hidden = (currentTab !== "home");
  rows.hidden = (currentTab !== "home");

  if (currentTab === "anime_series") { renderAnimeSeriesTab(); return; }
  if (currentTab === "web_series") { renderSeriesTab(); return; }
  if (currentTab === "anime_movies") { renderAnimeMoviesTab(); return; }
  if (currentTab === "movies") { renderMoviesTab(); return; }

  // HOME TAB
  if (!allMovies.length && !allSeries.length) {
    hero.hidden = true;
    rows.innerHTML = `<div class="empty" style="padding-top:140px"><h3>Your library is empty</h3><p>Add movie or web series folders to <code>${esc(data.root)}</code> and they will appear here.</p></div>`;
    return;
  }

  // Active watching items for the Continue Watching row below
  const watchingAll = all.filter(m => m.progress).sort((a, b) => b.progress.ts - a.progress.ts);

  // Helper to strictly deduplicate titles in the hero carousel
  function normalizeTitle(t) {
    return (t || "").toLowerCase().replace(/[^a-z0-9]/g, "");
  }

  // Hero Carousel Selection: Balanced mix across Web Series, Blockbuster Movies, Anime Movies, and Anime Series
  const pools = [
    [...(webSeries || [])],
    [...(movies || [])],
    [...(animeMovies || [])],
    [...(animeSeries || [])],
  ];

  const seenKeys = new Set();
  heroItems = [];
  let addedAny = true;
  while (heroItems.length < 10 && addedAny) {
    addedAny = false;
    for (const pool of pools) {
      while (pool.length > 0) {
        const it = pool.shift();
        const norm = normalizeTitle(it.title);
        const key = it.id || it.path || norm;
        if (norm && !seenKeys.has(norm) && !seenKeys.has(key)) {
          seenKeys.add(norm);
          seenKeys.add(key);
          heroItems.push(it);
          addedAny = true;
          break;
        }
      }
      if (heroItems.length >= 10) break;
    }
  }
  heroItem = heroItems[0] || null;

  hero.className = "hero";
  hero.innerHTML = heroCarouselHTML(heroItems);
  heroCurrentIdx = 0;
  bindHeroEvents();
  const heroTr = $("#heroTrack");
  if (heroTr && heroItems.length > 1) {
    const sls = heroTr.querySelectorAll(".hero-slide");
    if (sls[1]) jumpInstant(heroTr, sls[1].offsetLeft);
  }
  startHeroAuto();

  const out = [];
  // 1. Continue Watching
  out.push(rowHTML("continue", "Continue Watching", watchingAll, (m, i) => movieCard(m, i, { resume: true, clear: true })));

  // 2. Web Series & TV Shows Row
  if (webSeries.length) {
    out.push(rowHTML("web_series_row", "Web Series & TV Shows", webSeries, (s, i) => seriesCard(s, i)));
  }

  // 3. Blockbuster Movies Row
  if (movies.length) {
    out.push(rowHTML("movies_row", "Blockbuster Movies", movies, (m, i) => movieCard(m, i)));
  }

  // 4. Anime Movies Row
  if (animeMovies.length) {
    out.push(rowHTML("anime_movies_row", "Anime Movies", animeMovies, (m, i) => movieCard(m, i)));
  }

  // 5. Anime Web Series Row
  if (animeSeries.length) {
    out.push(rowHTML("anime_series_row", "Anime Web Series", animeSeries, (s, i) => seriesCard(s, i)));
  }

  // 6. 4K Ultra HD Row
  const uhd = all.filter(m => m.quality === "4K").sort(sorters.az);
  if (uhd.length) {
    out.push(rowHTML("uhd_row", "4K Ultra HD", uhd, (m, i) => movieCard(m, i)));
  }

  // 7. Recently Added Row
  const newest = [...movies, ...animeMovies].sort(sorters.new).slice(0, 16);
  if (newest.length) {
    out.push(rowHTML("new_row", "Recently Added Movies", newest, (m, i) => movieCard(m, i)));
  }
  rows.innerHTML = out.join("");

  document.querySelectorAll("[data-track]").forEach(t => { if (scroll[t.dataset.track]) t.scrollLeft = scroll[t.dataset.track]; updArrows(t); });
  document.querySelectorAll("img").forEach(i => { if (i.complete && i.naturalWidth) i.classList.add("ld"); });
  reveal();
  first = false;
}

function renderAnimeSeriesTab() {
  const series = data.anime_series || [];
  const chips = [["all", "All Anime"], ["multi", "Multi-Season"], ["4K", "4K Ultra HD"], ["1080p", "1080p Full HD"]];
  if (!chips.some(c => c[0] === animeSeriesFilter)) animeSeriesFilter = "all";
  $("#animeSeriesChips").innerHTML = chips.map(([k, l]) => `<button class="chip ${k === animeSeriesFilter ? "on" : ""}" data-asf="${k}">${l}</button>`).join("");
  const list = series.filter(s => {
    if (animeSeriesFilter === "multi") return s.seasonsCount > 1;
    if (animeSeriesFilter === "4K") return s.quality === "4K";
    if (animeSeriesFilter === "1080p") return s.quality === "1080p";
    return true;
  }).sort(sorters[animeSeriesSort] || sorters.az);
  $("#animeSeriesGrid").innerHTML = list.length ? list.map((s, i) => seriesCard(s, i)).join("") : '<div class="empty"><h3>No anime series found</h3></div>';
}

function renderSeriesTab() {
  const series = data.web_series || [];
  const chips = [["all", "All Series"], ["multi", "Multi-Season"], ["4K", "4K Ultra HD"], ["1080p", "1080p Full HD"]];
  if (!chips.some(c => c[0] === seriesFilter)) seriesFilter = "all";
  $("#seriesChips").innerHTML = chips.map(([k, l]) => `<button class="chip ${k === seriesFilter ? "on" : ""}" data-sf="${k}">${l}</button>`).join("");
  const list = series.filter(s => {
    if (seriesFilter === "multi") return s.seasonsCount > 1;
    if (seriesFilter === "4K") return s.quality === "4K";
    if (seriesFilter === "1080p") return s.quality === "1080p";
    return true;
  }).sort(sorters[seriesSort] || sorters.az);
  $("#seriesGrid").innerHTML = list.length ? list.map((s, i) => seriesCard(s, i)).join("") : '<div class="empty"><h3>No web series detected</h3></div>';
}

function renderAnimeMoviesTab() {
  const movies = data.anime_movies || [];
  const quals = ["4K", "1080p", "720p", "SD"].filter(q => movies.some(m => m.quality === q));
  const exts = [...new Set(movies.map(m => m.ext))].sort();
  const chips = [["all", "All Anime Movies"], ...quals.map(q => [q, q]), ...(exts.length > 1 ? exts.map(e => [e, e.slice(1).toUpperCase()]) : [])];
  if (!chips.some(c => c[0] === animeMovieFilter)) animeMovieFilter = "all";
  $("#animeMovieChips").innerHTML = chips.map(([k, l]) => `<button class="chip ${k === animeMovieFilter ? "on" : ""}" data-amf="${k}">${l}</button>`).join("");
  const list = movies.filter(m => animeMovieFilter === "all" || m.quality === animeMovieFilter || m.ext === animeMovieFilter).sort(sorters[animeMovieSort] || sorters.az);
  $("#animeMovieGrid").innerHTML = list.length ? list.map((m, i) => movieCard(m, i)).join("") : '<div class="empty"><h3>No anime movies found</h3></div>';
}

function renderMoviesTab() {
  const movies = data.movies || [];
  const quals = ["4K", "1080p", "720p", "SD"].filter(q => movies.some(m => m.quality === q));
  const exts = [...new Set(movies.map(m => m.ext))].sort();
  const chips = [["all", "All Movies"], ...quals.map(q => [q, q]), ...(exts.length > 1 ? exts.map(e => [e, e.slice(1).toUpperCase()]) : [])];
  if (!chips.some(c => c[0] === movieFilter)) movieFilter = "all";
  $("#movieChips").innerHTML = chips.map(([k, l]) => `<button class="chip ${k === movieFilter ? "on" : ""}" data-mf="${k}">${l}</button>`).join("");
  const list = movies.filter(m => movieFilter === "all" || m.quality === movieFilter || m.ext === movieFilter).sort(sorters[movieSort] || sorters.az);
  $("#movieGrid").innerHTML = list.length ? list.map((m, i) => movieCard(m, i)).join("") : '<div class="empty"><h3>No blockbuster movies found</h3></div>';
}

function renderResults() {
  if (!query) return;
  const q = query.toLowerCase();
  const all = data.all_items || [];
  const list = all.filter(m => (m.title + " " + (m.year || "") + " " + m.file + " " + (m.folder || "")).toLowerCase().includes(q)).sort(sorters.az);
  $("#resH").innerHTML = list.length ? `<b>${list.length}</b> ${list.length === 1 ? "result" : "results"} for "${esc(query)}"` : `Nothing matches "${esc(query)}".`;
  $("#resGrid").innerHTML = list.map((m, i) => movieCard(m, i)).join("");
  document.querySelectorAll("#resGrid img").forEach(i => { if (i.complete && i.naturalWidth) i.classList.add("ld"); });
}

function foot() {
  const d = data;
  const as = (d.anime_series || []).length;
  const ws = (d.web_series || []).length;
  const am = (d.anime_movies || []).length;
  const m = (d.movies || []).length;
  $("#foot").innerHTML = `<span>${as} anime series, ${ws} web series, ${am} anime movies, ${m} movies • ${gb(d.total_size)} GB</span>` +
    (d.scanning ? `<span class="live">Indexing ${d.scanned} of ${d.to_scan}</span>` : "");
}

/* ---------- NETFLIX MOVIE MODAL ---------- */
function openMovieModal(m) {
  $("#movieModalTitle").textContent = m.title;
  const p = m.progress, pct = p && p.dur ? Math.min(100, p.pos / p.dur * 100) : 0;
  const parts = [
    m.year ? `<span>${esc(m.year)}</span>` : "",
    m.duration ? `<span>${dur(m.duration)}</span>` : "",
    m.vcodec ? `<span class="pill">${esc(m.vcodec)}</span>` : "",
    `<span>${gb(m.size)} GB</span>`
  ].filter(Boolean);
  $("#movieModalMeta").innerHTML = parts.join(" • ");
  const qBadge = $("#movieModalQualityBadge");
  if (qBadge) qBadge.textContent = m.quality || "HD";

  const isAnime = m.category === "anime_movies";
  const badgeEl = $("#movieModalBadge");
  if (badgeEl) {
    badgeEl.textContent = isAnime ? "ANIME MOVIE" : "MOVIE";
    badgeEl.style.background = isAnime ? "#d946ef" : "var(--accent)";
  }

  const thumbUrl = `/thumb/${encPath(m.path)}?w=1280&v=${m.mtime}`;
  const bg = $("#movieModalBg");
  bg.classList.remove("ld");
  bg.src = thumbUrl;
  if (bg.complete && bg.naturalWidth) bg.classList.add("ld");

  const poster = $("#movieModalPoster");
  if (poster) {
    poster.classList.remove("ld");
    poster.src = thumbUrl;
    if (poster.complete && poster.naturalWidth) poster.classList.add("ld");
  }

  $("#movieModalPlay").href = `/player/${encPath(m.path)}`;
  $("#movieModalCopy").dataset.copy = m.path;

  const resumeBtn = $("#movieModalResume");
  const playBtn = $("#movieModalPlay");
  if (p && p.pos > 15) {
    resumeBtn.hidden = false;
    resumeBtn.className = "btn pri";
    resumeBtn.innerHTML = `${ic("play")}Resume from ${dur(p.pos)}`;
    resumeBtn.href = `/player/${encPath(m.path)}`;
    playBtn.className = "btn ghost";
    playBtn.innerHTML = `${ic("play")}Start from Beginning`;
    playBtn.href = `/player/${encPath(m.path)}?t=0`;
  } else {
    resumeBtn.hidden = true;
    playBtn.className = "btn pri";
    playBtn.innerHTML = `${ic("play")}Play Movie`;
    playBtn.href = `/player/${encPath(m.path)}`;
  }

  // Audio list
  const audList = $("#movieModalAudio");
  if (m.audio && m.audio.length) {
    audList.innerHTML = m.audio.map(a => `<span class="audio-chip">${esc(a)}</span>`).join("");
  } else {
    audList.innerHTML = '<span class="spec-val">Stereo (Default)</span>';
  }

  $("#movieModalQuality").textContent = `${m.quality || "HD"} • ${m.vcodec || "H.264"}`;
  $("#movieModalFile").textContent = `${m.file} (${m.folder || "Root"})`;

  // More like this row
  const allMovies = data.all_movies || [...(data.movies || []), ...(data.anime_movies || [])];
  const others = allMovies.filter(x => x.path !== m.path).sort(sorters.new).slice(0, 10);
  const track = $("#movieRelatedTrack");
  if (others.length) {
    $("#movieRelatedSec").hidden = false;
    track.innerHTML = others.map((it, i) => movieCard(it, i)).join("");
  } else {
    $("#movieRelatedSec").hidden = true;
  }

  $("#movieModal").classList.add("open");
  document.body.style.overflow = "hidden";
  stopHeroAuto();
}

function closeMovieModal() {
  $("#movieModal").classList.remove("open");
  document.body.style.overflow = "";
  if (currentTab === "home") startHeroAuto();
}

/* ---------- NETFLIX WEB SERIES MODAL ---------- */
function openSeriesModal(s) {
  activeSeries = s;
  activeSeasonId = (s.latestProgress && s.latestProgress.seasonId) || (s.seasons[0] ? s.seasons[0].id : "");
  $("#seriesModalTitle").textContent = s.title;

  const parts = [
    s.year ? `<span>${esc(s.year)}</span>` : "",
    `<span>${s.seasonsCount} ${s.seasonsCount > 1 ? "Seasons" : "Season"}</span>`,
    `<span>${s.totalEpisodes} Episodes</span>`,
    `<span>${gb(s.totalSize)} GB</span>`
  ].filter(Boolean);
  $("#seriesModalMeta").innerHTML = parts.join(" • ");
  const qBadge = $("#seriesModalQualityBadge");
  if (qBadge) qBadge.textContent = s.quality || "HD";

  const isAnime = s.category === "anime_series";
  const badgeEl = $("#seriesModalBadge");
  if (badgeEl) {
    badgeEl.textContent = isAnime ? "ANIME SERIES" : "WEB SERIES";
    badgeEl.style.background = isAnime ? "#e11d48" : "var(--series)";
  }

  const thumbUrl = `/thumb/${encPath(s.posterPath)}?w=1280&v=${s.added}`;
  const sbg = $("#seriesModalBg");
  sbg.classList.remove("ld");
  sbg.src = thumbUrl;
  if (sbg.complete && sbg.naturalWidth) sbg.classList.add("ld");

  const spost = $("#seriesModalPoster");
  if (spost) {
    spost.classList.remove("ld");
    spost.src = thumbUrl;
    if (spost.complete && spost.naturalWidth) spost.classList.add("ld");
  }

  const firstEp = (s.seasons[0] && s.seasons[0].episodes[0]) ? s.seasons[0].episodes[0].path : s.posterPath;
  const playTarget = (s.latestProgress && s.latestProgress.path) || firstEp;
  $("#seriesModalPlay").href = `/player/${encPath(playTarget)}`;
  $("#seriesModalPlay").innerHTML = `${ic("play")}${s.latestProgress ? `Resume ${s.latestProgress.epTitle || 'Episode'}` : "Play Now"}`;
  $("#seriesModalCopy").dataset.copy = playTarget;

  // Render season tabs
  const tabsWrap = $("#seasonTabs");
  tabsWrap.innerHTML = s.seasons.map(sea => `<button class="season-tab ${sea.id === activeSeasonId ? "on" : ""}" data-sid="${esc(sea.id)}">${esc(sea.name)}</button>`).join("");

  renderSeasonEpisodes();
  $("#seriesModal").classList.add("open");
  document.body.style.overflow = "hidden";
  stopHeroAuto();
}

function renderSeasonEpisodes() {
  if (!activeSeries) return;
  const season = activeSeries.seasons.find(sea => sea.id === activeSeasonId) || activeSeries.seasons[0];
  if (!season) return;
  const epList = $("#episodesList");
  epList.innerHTML = season.episodes.map(ep => {
    const p = ep.progress, pct = p && p.dur ? Math.min(100, p.pos / p.dur * 100) : 0;
    const durStr = dur(ep.duration);
    const subStr = [ep.quality, ep.audio && ep.audio[0], gb(ep.size) + " GB"].filter(Boolean).join(" • ");
    return `<div class="ep-row" data-path="${esc(ep.path)}" tabindex="0" role="link" aria-label="Play ${esc(ep.title)}">
      <div class="ep-num">${ep.episodeNumber || ""}</div>
      <div class="ep-thumb-wrap">
        <img class="ep-thumb" src="/thumb/${encPath(ep.path)}" alt="" loading="lazy" onload="this.classList.add('ld')">
        <div class="ep-play-overlay">${ic("play")}</div>
        ${pct ? `<div class="pbar"><i style="width:${pct}%"></i></div>` : ""}
      </div>
      <div class="ep-details">
        <div class="ep-header-line">
          <div class="ep-name">${esc(ep.fullTitle || ep.title)}</div>
          <div class="ep-dur">${durStr}</div>
        </div>
        <div class="ep-sub">${esc(subStr)}</div>
      </div>
      <button class="ep-copy-btn" data-copy="${esc(ep.path)}" title="Copy stream link" aria-label="Copy stream link">${ic("link")}</button>
    </div>`;
  }).join("");
}

function switchSeason(sid) {
  activeSeasonId = sid;
  document.querySelectorAll(".season-tab").forEach(tab => tab.classList.toggle("on", tab.dataset.sid === sid));
  renderSeasonEpisodes();
}

function closeSeriesModal() {
  $("#seriesModal").classList.remove("open");
  document.body.style.overflow = "";
  if (currentTab === "home") startHeroAuto();
}

/* ---------- row scrolling arrows ---------- */
function updArrows(t) {
  const row = t.closest(".row"); if (!row) return;
  row.querySelector(".arrow.l").classList.toggle("on", t.scrollLeft > 8);
  row.querySelector(".arrow.r").classList.toggle("on", t.scrollLeft + t.clientWidth < t.scrollWidth - 8);
}
const io = "IntersectionObserver" in window ? new IntersectionObserver(es => es.forEach(e => { if (e.isIntersecting) { e.target.classList.add("in"); io.unobserve(e.target); } }), { rootMargin: "0px 0px -8% 0px" }) : null;
function reveal() { document.querySelectorAll(".row.pre").forEach(r => io ? io.observe(r) : r.classList.add("in")); }

/* ---------- event delegation ---------- */
document.addEventListener("click", e => {
  const t = e.target;

  // Close modals
  if (t.closest("#movieModalClose") || t.id === "movieModal") { closeMovieModal(); return; }
  if (t.closest("#seriesModalClose") || t.id === "seriesModal") { closeSeriesModal(); return; }

  // Episode copy button
  const epCp = t.closest(".ep-copy-btn");
  if (epCp) {
    e.stopPropagation();
    copyLink(location.origin + "/stream/" + encPath(epCp.dataset.copy));
    return;
  }

  // Episode click -> play
  const epRow = t.closest(".ep-row");
  if (epRow) {
    location.href = "/player/" + encPath(epRow.dataset.path);
    return;
  }

  // Season tab click
  const stab = t.closest(".season-tab");
  if (stab) {
    switchSeason(stab.dataset.sid);
    return;
  }

  // Poster click inside Movie Detail Modal -> play movie
  if (t.closest("#movieModalPosterCard")) {
    const r = $("#movieModalResume");
    const playTarget = (!r.hidden && r.href) ? r.href : $("#movieModalPlay").href;
    if (playTarget) location.href = playTarget;
    return;
  }

  // Poster click inside Series Detail Modal -> play series
  if (t.closest("#seriesModalPosterCard")) {
    const playTarget = $("#seriesModalPlay").href;
    if (playTarget) location.href = playTarget;
    return;
  }

  // Arrow click for row scrolling
  const ar = t.closest(".arrow");
  if (ar) { const tr = ar.parentElement.querySelector(".track"); tr.scrollBy({ left: (ar.classList.contains("l") ? -1 : 1) * tr.clientWidth * .85, behavior: "smooth" }); return; }

  // Copy link button
  const cp = t.closest("[data-copy]");
  if (cp) { e.stopPropagation(); copyLink(location.origin + "/stream/" + encPath(cp.dataset.copy)); return; }

  // Clear continue watching progress
  const cl = t.closest("[data-clear]");
  if (cl) {
    e.stopPropagation();
    const path = cl.dataset.clear;
    fetch("/api/progress", { method: "POST", body: JSON.stringify({ path, clear: true }) }).then(() => {
      const all = data.all_items || [];
      const it = all.find(x => x.path === path);
      if (it) it.progress = null;
      sig = ""; load();
    });
    return;
  }

  // Hero Play button -> plays immediately
  const heroPlay = t.closest(".hero-btn-play, #heroPlayBtn");
  if (heroPlay) {
    const target = heroPlay.dataset.target;
    if (target) {
      location.href = "/player/" + encPath(target);
      return;
    }
    const current = (heroItems && heroItems[heroCurrentIdx]) || heroItem;
    if (current) {
      const playTarget = current.seasonsCount ? ((current.latestProgress && current.latestProgress.path) || (current.seasons[0] && current.seasons[0].episodes[0] && current.seasons[0].episodes[0].path) || current.posterPath) : current.path;
      if (playTarget) location.href = "/player/" + encPath(playTarget);
    }
    return;
  }

  // Hero Info button -> opens detail modal
  const heroInfo = t.closest(".hero-btn-info, #heroInfoBtn");
  if (heroInfo) {
    const type = heroInfo.dataset.type;
    const id = heroInfo.dataset.id;
    if (type === "series") {
      const allSeries = data.all_series || [...(data.anime_series || []), ...(data.web_series || [])];
      const s = allSeries.find(x => x.id === id);
      if (s) { openSeriesModal(s); return; }
    } else if (type === "movie") {
      const allMovies = data.all_movies || [...(data.movies || []), ...(data.anime_movies || []), ...(data.all_items || [])];
      const m = allMovies.find(x => x.path === id);
      if (m) { openMovieModal(m); return; }
    }
    const current = (heroItems && heroItems[heroCurrentIdx]) || heroItem;
    if (current) {
      if (current.seasonsCount) openSeriesModal(current);
      else openMovieModal(current);
    }
    return;
  }

  // Surprise me button
  if (t.closest(".hero-btn-surprise, #surprise")) {
    const all = data.all_items || [];
    if (all.length) {
      const pick = all[Math.floor(Math.random() * all.length)];
      location.href = "/player/" + encPath(pick.path);
    }
    return;
  }

  // Card click -> Continue Watching plays right away; all other cards open Netflix Detail Modal!
  const c = t.closest(".card");
  if (c) {
    if (c.dataset.resume === "1") {
      location.href = "/player/" + encPath(c.dataset.p);
      return;
    }
    if (c.dataset.type === "series") {
      const allSeries = data.all_series || [...(data.anime_series || []), ...(data.web_series || []), ...(data.series || [])];
      const s = allSeries.find(x => x.id === c.dataset.seriesId);
      if (s) openSeriesModal(s);
    } else {
      const allMovies = data.all_movies || [...(data.movies || []), ...(data.anime_movies || []), ...(data.all_items || [])];
      const m = allMovies.find(x => x.path === c.dataset.p);
      if (m) openMovieModal(m);
      else location.href = "/player/" + encPath(c.dataset.p);
    }
    return;
  }

  // Filter chips in tabs
  const asf = t.closest("[data-asf]");
  if (asf) { animeSeriesFilter = asf.dataset.asf; renderAnimeSeriesTab(); return; }
  const sf = t.closest("[data-sf]");
  if (sf) { seriesFilter = sf.dataset.sf; renderSeriesTab(); return; }
  const amf = t.closest("[data-amf]");
  if (amf) { animeMovieFilter = amf.dataset.amf; renderAnimeMoviesTab(); return; }
  const mf = t.closest("[data-mf]");
  if (mf) { movieFilter = mf.dataset.mf; renderMoviesTab(); return; }

});

/* Navigation Links */
function setTab(tab) {
  currentTab = tab;
  closeSearch(true);
  closeMovieModal();
  closeSeriesModal();
  if (tab !== "home") stopHeroAuto();
  render();
  scrollTo({ top: 0, behavior: "smooth" });
}

window.addEventListener("resize", () => {
  const track = $("#heroTrack");
  if (track && heroItems.length) {
    const slides = track.querySelectorAll(".hero-slide");
    const targetIdx = heroItems.length > 1 ? heroCurrentIdx + 1 : 0;
    const target = slides[targetIdx];
    if (target) jumpInstant(track, target.offsetLeft);
  }
});
document.addEventListener("visibilitychange", () => {
  if (document.hidden) stopHeroAuto();
  else if (currentTab === "home") startHeroAuto();
});

$("#lnkHome").addEventListener("click", e => { e.preventDefault(); setTab("home"); });
$("#lnkAnimeSeries").addEventListener("click", e => { e.preventDefault(); setTab("anime_series"); });
$("#lnkSeries").addEventListener("click", e => { e.preventDefault(); setTab("web_series"); });
$("#lnkAnimeMovies").addEventListener("click", e => { e.preventDefault(); setTab("anime_movies"); });
$("#lnkMovies").addEventListener("click", e => { e.preventDefault(); setTab("movies"); });

$("#animeSeriesSort").addEventListener("change", e => { animeSeriesSort = e.target.value; renderAnimeSeriesTab(); });
$("#seriesSort").addEventListener("change", e => { seriesSort = e.target.value; renderSeriesTab(); });
$("#animeMovieSort").addEventListener("change", e => { animeMovieSort = e.target.value; renderAnimeMoviesTab(); });
$("#movieSort").addEventListener("change", e => { movieSort = e.target.value; renderMoviesTab(); });

document.addEventListener("keydown", e => {
  if (e.key === "Escape") { closeSearch(true); closeQr(); closeMovieModal(); closeSeriesModal(); }
  if (e.key === "/" && document.activeElement !== $("#q")) { e.preventDefault(); openSearch(); }
});
document.addEventListener("scroll", e => { if (e.target.classList && e.target.classList.contains("track")) updArrows(e.target); }, true);
addEventListener("scroll", () => $("#nav").classList.toggle("solid", scrollY > 24), { passive: true });

/* Search handling */
const search = $("#search"), qi = $("#q");
function openSearch() { search.classList.add("open"); qi.focus(); }
function closeSearch(clear) { if (clear) { qi.value = ""; setQuery(""); } if (!qi.value) search.classList.remove("open"); }
function setQuery(v) { query = v.trim(); document.body.classList.toggle("searching", !!query); if (query) { renderResults(); scrollTo({ top: 0 }); } }
$("#searchBtn").addEventListener("click", () => search.classList.contains("open") && !qi.value ? closeSearch() : openSearch());
qi.addEventListener("input", () => setQuery(qi.value));
qi.addEventListener("blur", () => closeSearch());

/* Toast & QR Modal */
let tt;
function toast(msg) { const t = $("#toast"); t.textContent = msg; t.classList.add("show"); clearTimeout(tt); tt = setTimeout(() => t.classList.remove("show"), 2600); }
function copyLink(text) {
  const done = () => toast("Stream link copied. Paste into VLC on iPad.");
  if (navigator.clipboard && window.isSecureContext) { navigator.clipboard.writeText(text).then(done, () => legacyCopy(text, done)); }
  else legacyCopy(text, done);
}
function legacyCopy(text, done) {
  const ta = document.createElement("textarea"); ta.value = text; ta.style.cssText = "position:fixed;opacity:0;top:0"; document.body.appendChild(ta);
  ta.focus(); ta.select(); ta.setSelectionRange(0, 99999);
  let ok = false; try { ok = document.execCommand("copy"); } catch (e) {}
  ta.remove(); ok ? done() : toast("Copy failed.");
}
function openQr() {
  const url = `http://${data ? data.ip : location.hostname}:${data ? data.port : location.port}`;
  $("#qrUrl").textContent = url; $("#qrImg").style.display = "";
  $("#qrImg").src = "https://api.qrserver.com/v1/create-qr-code/?size=420x420&margin=0&data=" + encodeURIComponent(url);
  $("#qr").classList.add("open");
}
function closeQr() { $("#qr").classList.remove("open"); }
$("#connectBtn").addEventListener("click", openQr);
$("#qrClose").addEventListener("click", closeQr);
$("#qr").addEventListener("click", e => { if (e.target.id === "qr") closeQr(); });

addEventListener("pageshow", e => { if (e.persisted) { sig = ""; load(); } });
load();
})();
</script>
</body>
</html>
"""

PLAYER_HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1, user-scalable=no, viewport-fit=cover">
<meta name="theme-color" content="#000000">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="mobile-web-app-capable" content="yes">
<title>__PAGE_TITLE__ - __APP__</title>
<link rel="icon" href="/favicon.svg" type="image/svg+xml">
<style>
:root{--accent:#ff7a1a;--ease:cubic-bezier(.22,.8,.24,1);
  --font:-apple-system,BlinkMacSystemFont,"SF Pro Display","Segoe UI Variable Display","Segoe UI",Roboto,Helvetica,Arial,sans-serif;
  --sl:max(24px,env(safe-area-inset-left));--sr:max(24px,env(safe-area-inset-right))}
*{box-sizing:border-box;margin:0;padding:0;-webkit-tap-highlight-color:transparent}
html,body{height:100%;background:#000;color:#fff;font:400 15px/1.4 var(--font);overflow:hidden;overscroll-behavior:none;-webkit-font-smoothing:antialiased}
a{color:inherit;text-decoration:none}
button{font:inherit;color:inherit;background:none;border:0;cursor:pointer}
:focus-visible{outline:2px solid var(--accent);outline-offset:2px}
svg{display:block;flex:none}

.app{position:fixed;inset:0;background:#000;overflow:hidden;-webkit-user-select:none;user-select:none;touch-action:none}
video{position:absolute;left:0;top:0;width:100%;height:100%;object-fit:contain;background:#000;transition:filter .12s}
#gest{position:absolute;inset:0;z-index:5;touch-action:none}

/* bars */
.bar{position:absolute;left:0;right:0;z-index:20;transition:opacity .35s,transform .45s var(--ease)}
.top{top:0;display:flex;align-items:center;gap:12px;padding:calc(14px + env(safe-area-inset-top)) var(--sr) 44px var(--sl);background:linear-gradient(#000000d1,#0000)}
.bottom{bottom:0;padding:60px var(--sr) calc(14px + env(safe-area-inset-bottom)) var(--sl);background:linear-gradient(0deg,#000000eb 12%,#0000)}
.app.idle .top{opacity:0;transform:translateY(-14px);pointer-events:none}
.app.idle .bottom{opacity:0;transform:translateY(14px);pointer-events:none}
.app.idle{cursor:none}
.ttl{min-width:0;flex:1;display:flex;flex-direction:column}
.ttl b{font-size:18px;font-weight:700;letter-spacing:-.01em;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.ttl span{font-size:13px;color:#ffffff99;min-height:1.3em}
.chip{font-size:12.5px;font-weight:600;color:#ffffffcc;padding:4px 10px;border-radius:999px;background:#ffffff1f;white-space:nowrap}
.chip:empty{display:none}

/* buttons */
.cb{width:44px;height:44px;border-radius:50%;display:grid;place-items:center;color:#fff;transition:background .2s,transform .15s,color .2s}
.cb:hover{background:#ffffff26}.cb:active{transform:scale(.9)}.cb.on{color:var(--accent)}
.cb[hidden]{display:none}
.cb.txt{width:auto;min-width:44px;padding:0 10px;border-radius:22px;font-size:14px;font-weight:700;font-variant-numeric:tabular-nums}
.row{display:flex;align-items:center;justify-content:space-between;gap:8px}
.grp{display:flex;align-items:center;gap:2px}
.time{font-size:14px;font-variant-numeric:tabular-nums;color:#ffffffa6;padding:6px 10px;border-radius:6px;cursor:pointer;white-space:nowrap}
.time b{color:#fff;font-weight:600}.time:hover{background:#ffffff1a}
.vol{display:flex;align-items:center}
.vol input{width:0;opacity:0;margin:0;transition:width .35s var(--ease),opacity .2s,margin .35s var(--ease)}
@media(hover:hover){.vol:hover input,.vol:focus-within input{width:92px;opacity:1;margin:0 8px 0 2px}}
input[type=range]{-webkit-appearance:none;appearance:none;height:4px;border-radius:2px;background:linear-gradient(90deg,#fff var(--p,100%),#ffffff40 var(--p,100%));outline:0;cursor:pointer}
input[type=range]::-webkit-slider-thumb{-webkit-appearance:none;width:13px;height:13px;border-radius:50%;background:#fff;border:0}
input[type=range]::-moz-range-thumb{width:13px;height:13px;border-radius:50%;background:#fff;border:0}

/* timeline */
.tl{position:relative;height:30px;display:flex;align-items:center;cursor:pointer;touch-action:none}
.track{position:relative;width:100%;height:4px;border-radius:2px;background:#ffffff40;transition:height .15s}
.tl:hover .track,.tl.drag .track{height:7px}
.buf,.prog{position:absolute;left:0;top:0;bottom:0;border-radius:inherit;width:0}
.buf{background:#ffffff59}
.prog{background:var(--accent);transition:width .25s linear}
.knob{position:absolute;top:50%;left:0;width:15px;height:15px;margin:-7.5px 0 0 -7.5px;border-radius:50%;background:var(--accent);box-shadow:0 0 0 4px #ff7a1a40;transform:scale(0);transition:transform .15s,left .25s linear}
.tl:hover .knob,.tl.drag .knob{transform:scale(1)}
.tl.drag .prog,.tl.drag .knob{transition:none}
.tip{position:absolute;bottom:28px;left:0;transform:translateX(-50%);background:#000000d9;padding:3px 9px;border-radius:6px;font-size:12.5px;font-weight:600;font-variant-numeric:tabular-nums;opacity:0;pointer-events:none;transition:opacity .15s}
.mini{position:absolute;left:0;right:0;bottom:0;height:3px;background:#ffffff2e;z-index:15;opacity:0;transition:opacity .35s;pointer-events:none}
.mini i{display:block;height:100%;width:0;background:var(--accent)}
.app.idle .mini{opacity:1}

/* popovers */
.pop{position:absolute;right:var(--sr);bottom:calc(96px + env(safe-area-inset-bottom));z-index:30;min-width:230px;max-width:calc(100vw - 28px);max-height:62vh;overflow:auto;background:#16161af2;backdrop-filter:blur(22px);-webkit-backdrop-filter:blur(22px);border:1px solid #ffffff1f;border-radius:14px;padding:8px;box-shadow:0 20px 50px #000a;
  opacity:0;visibility:hidden;transform:translateY(12px) scale(.97);transform-origin:bottom right;transition:opacity .2s,transform .35s var(--ease),visibility 0s .35s}
.pop.open{opacity:1;visibility:visible;transform:none;transition:opacity .2s,transform .35s var(--ease)}
.pop h4{font-size:12px;font-weight:700;color:#ffffff80;letter-spacing:.08em;text-transform:uppercase;padding:8px 10px 6px}
.item{display:flex;align-items:center;justify-content:space-between;gap:12px;width:100%;padding:10px 12px;border-radius:8px;font-size:14px;font-weight:500;text-align:left;transition:background .15s}
.item:hover{background:#ffffff1f}.item.on{color:var(--accent);font-weight:700}
.seg{display:flex;background:#0c0c0f;padding:3px;border-radius:8px;margin:4px 6px 12px;gap:2px}
.seg button{flex:1;padding:7px;border-radius:6px;font-size:12.5px;font-weight:600;color:#ffffff99;transition:all .15s}
.seg button.on{background:#ffffff26;color:#fff}
.fx{display:flex;align-items:center;justify-content:space-between;gap:14px;padding:8px 10px;font-size:13.5px;color:#ffffffcc}
.fx input{flex:1;max-width:130px}
.fx output{width:40px;text-align:right;font-variant-numeric:tabular-nums;color:#fff}
.reset{margin:8px 10px;padding:8px;width:calc(100% - 20px);border-radius:6px;background:#ffffff14;font-size:13px;font-weight:600}

/* gestures & HUD */
.flash{position:absolute;inset:0;background:#000;opacity:0;pointer-events:none;transition:opacity .35s;z-index:4}
.rip{position:absolute;top:0;bottom:0;width:34%;display:flex;flex-direction:column;align-items:center;justify-content:center;gap:6px;color:#fff;opacity:0;pointer-events:none;transition:opacity .3s;z-index:6}
.rip.l{left:0;background:radial-gradient(ellipse at 0 50%,#ffffff30 0%,#0000 68%)}
.rip.r{right:0;background:radial-gradient(ellipse at 100 50%,#ffffff30 0%,#0000 68%)}
.rip span:last-child{font-size:13px;font-weight:700}
.rip.show{opacity:1}
.hud{position:absolute;top:50%;left:50%;transform:translate(-50%,-50%) scale(.9);background:#000000c7;backdrop-filter:blur(14px);-webkit-backdrop-filter:blur(14px);border-radius:18px;padding:18px 22px;display:flex;flex-direction:column;align-items:center;gap:12px;opacity:0;pointer-events:none;transition:opacity .2s,transform .2s var(--ease);z-index:25}
.hud.show{opacity:1;transform:translate(-50%,-50%)}
.hud .t{width:140px;height:5px;border-radius:3px;background:#ffffff33;overflow:hidden}
.hud .t i{display:block;height:100%;background:var(--accent);width:50%}
.hud .val{font-size:14px;font-weight:700;font-variant-numeric:tabular-nums}
.osd{position:absolute;top:calc(74px + env(safe-area-inset-top));left:50%;transform:translate(-50%,-10px);background:#000000d1;backdrop-filter:blur(12px);border-radius:999px;padding:8px 18px;font-size:14px;font-weight:600;opacity:0;pointer-events:none;transition:opacity .25s,transform .25s;z-index:25}
.osd.show{opacity:1;transform:translate(-50%,0)}
.spin{position:absolute;inset:0;display:grid;place-items:center;gap:14px;background:#00000066;backdrop-filter:blur(4px);z-index:8;opacity:0;pointer-events:none;transition:opacity .3s}
.spin.show{opacity:1;pointer-events:auto}
.spin i{width:46px;height:46px;border-radius:50%;border:3.5px solid #ffffff33;border-top-color:var(--accent);animation:sp .8s linear infinite}
@keyframes sp{to{transform:rotate(360deg)}}
.spin span{font-size:14px;font-weight:600;color:#ffffffcc}
.big{position:absolute;top:50%;left:50%;transform:translate(-50%,-50%) scale(.7);width:80px;height:80px;border-radius:50%;background:#000000a6;backdrop-filter:blur(12px);display:grid;place-items:center;z-index:12;opacity:0;pointer-events:none;transition:opacity .35s,transform .35s var(--ease)}
.big.show{opacity:1;transform:translate(-50%,-50%)}
.lock{position:absolute;top:calc(16px + env(safe-area-inset-top));left:50%;transform:translateX(-50%);background:#16161af0;backdrop-filter:blur(14px);border:1px solid #ffffff26;border-radius:999px;padding:10px 22px;display:none;align-items:center;gap:10px;font-size:14px;font-weight:600;z-index:40;cursor:pointer}
.lock.on{display:flex}
.toast{position:absolute;bottom:calc(96px + env(safe-area-inset-bottom));left:50%;transform:translate(-50%,20px);background:#16161af2;backdrop-filter:blur(16px);border:1px solid #ffffff26;border-radius:999px;padding:8px 10px 8px 18px;display:flex;align-items:center;gap:14px;font-size:14px;font-weight:600;opacity:0;pointer-events:none;transition:opacity .3s,transform .35s var(--ease);z-index:35}
.toast.show{opacity:1;transform:translate(-50%,0);pointer-events:auto}
.toast button{background:#fff;color:#000;padding:6px 14px;border-radius:999px;font-weight:700;font-size:13px}

/* Next Episode Floating Card */
.next-card{position:absolute;right:var(--sr);bottom:calc(100px + env(safe-area-inset-bottom));z-index:45;background:#16161af5;backdrop-filter:blur(20px);-webkit-backdrop-filter:blur(20px);border:1px solid var(--accent);border-radius:14px;padding:14px 18px;display:flex;align-items:center;gap:16px;box-shadow:0 16px 40px #000c;transform:translateY(20px);opacity:0;pointer-events:none;transition:transform .4s var(--ease),opacity .3s}
.next-card.show{transform:none;opacity:1;pointer-events:auto}
.next-info{display:flex;flex-direction:column;gap:2px}
.next-label{font-size:12px;font-weight:700;color:var(--accent);letter-spacing:.06em;text-transform:uppercase}
.next-title{font-size:14.5px;font-weight:700;color:#fff;max-width:240px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.next-actions{display:flex;align-items:center;gap:8px}
.next-btn{background:#fff;color:#000;font-weight:700;font-size:13.5px;padding:8px 16px;border-radius:8px;display:inline-flex;align-items:center;gap:6px}
.next-cancel{color:var(--muted);font-size:13px;padding:6px 8px}

.err{position:absolute;inset:0;background:#000000e6;z-index:50;display:none;flex-direction:column;align-items:center;justify-content:center;gap:16px;padding:24px;text-align:center}
.err.show{display:flex}
.err h3{font-size:22px;font-weight:700}
.err p{max-width:520px;color:#ffffffa6;font-size:14.5px;line-height:1.5}
.err .btn{background:var(--accent);color:#000;font-weight:700;padding:12px 28px;border-radius:8px;margin-top:8px}
</style>
<script src="/static/hls.js"></script>
</head>
<body>
<div class="app" id="app">
  <video id="v" playsinline webkit-playsinline preload="auto"></video>
  <div id="gest"></div>

  <div class="bar top" id="top">
    <a class="cb" href="/" id="back" aria-label="Back to library" title="Back to library"><span data-i="back" data-s="26"></span></a>
    <div class="ttl"><b id="title"></b><span id="sub"></span></div>
    <span class="chip" id="how"></span>
    <span class="time ends" id="ends" style="cursor:default"></span>
  </div>

  <div class="flash" id="flash"></div>
  <div class="rip l" id="ripL"><span data-i="chevL" data-s="30"></span><span id="ripLt"></span></div>
  <div class="rip r" id="ripR"><span data-i="chevR" data-s="30"></span><span id="ripRt"></span></div>
  <div class="hud" id="hud"><span data-hi></span><div class="t"><i></i></div><span class="val"></span></div>
  <div class="osd" id="osd"></div>
  <div class="spin" id="spin"><i></i><span id="spinT">Starting...</span></div>
  <button class="big" id="big" aria-label="Play or pause"><span data-i="play" data-s="34"></span></button>
  <div class="toast" id="toast"><span id="toastT"></span><button id="toastB"></button></div>
  <div class="lock" id="lockPill"><span data-i="lock" data-s="16"></span>Controls locked. Tap to unlock</div>
  <div class="mini"><i id="mini"></i></div>

  <!-- NEXT EPISODE COUNTDOWN CARD -->
  <div class="next-card" id="nextCard">
    <div class="next-info">
      <div class="next-label" id="nextLabel">Next Episode in 5s</div>
      <div class="next-title" id="nextTitle">Loading...</div>
    </div>
    <div class="next-actions">
      <button class="next-btn" id="btnPlayNext"><span data-i="play" data-s="16"></span>Play</button>
      <button class="next-cancel" id="btnCancelNext">Dismiss</button>
    </div>
  </div>

  <div class="bar bottom" id="bottom">
    <div class="tl" id="tl">
      <div class="track"><div class="buf" id="buf"></div><div class="prog" id="prog"></div><div class="knob" id="knob"></div></div>
      <div class="tip" id="tip">0:00</div>
    </div>
    <div class="row">
      <div class="grp">
        <button class="cb" id="bPlay" aria-label="Play or pause" title="Play / Pause (space)"><span data-i="play" data-s="28"></span></button>
        <button class="cb" id="bBack" aria-label="Back 10 seconds" title="Back 10 seconds"><span data-i="back10" data-s="28"></span></button>
        <button class="cb" id="bFwd" aria-label="Forward 10 seconds" title="Forward 10 seconds"><span data-i="fwd10" data-s="28"></span></button>
        <!-- NEXT EPISODE BUTTON (FOR WEB SERIES) -->
        <button class="cb" id="bNext" aria-label="Next episode" title="Next Episode" hidden><svg width="22" height="22" viewBox="0 0 24 24" fill="currentColor"><polygon points="5 4 15 12 5 20 5 4"/><rect x="17" y="4" width="3" height="16"/></svg></button>
        <div class="vol" id="volWrap">
          <button class="cb" id="bMute" aria-label="Mute" title="Mute (m)"><span id="volIc"></span></button>
          <input type="range" id="vol" min="0" max="1" step="0.02" value="1" aria-label="Volume">
        </div>
        <div class="time" id="time" title="Click to switch between total and remaining time"><b id="tCur">0:00</b> / <span id="tTot">0:00</span></div>
      </div>
      <div class="grp">
        <button class="cb" id="bLock" aria-label="Lock controls" title="Lock controls"><span data-i="unlock" data-s="22"></span></button>
        <button class="cb" id="bAudio" aria-label="Audio tracks" title="Audio" hidden><span data-i="audio" data-s="24"></span></button>
        <button class="cb txt" id="bSpeed" aria-label="Playback speed" title="Speed">1x</button>
        <button class="cb" id="bPic" aria-label="Picture settings" title="Picture"><span data-i="sliders" data-s="22"></span></button>
        <button class="cb" id="bPip" aria-label="Picture in picture" title="Picture in picture" hidden><span data-i="pip" data-s="22"></span></button>
        <button class="cb" id="bFs" aria-label="Fullscreen" title="Fullscreen (f)"><span data-i="max" data-s="24"></span></button>
      </div>
    </div>
  </div>

  <div class="pop" id="popAudio"><h4>Audio</h4><div id="audioList"></div></div>
  <div class="pop" id="popSpeed" style="min-width:170px"><h4>Speed</h4><div id="speedList"></div></div>
  <div class="pop" id="popPic" style="min-width:300px">
    <h4>Aspect ratio</h4><div class="seg" id="aspectList"></div>
    <h4>Picture</h4>
    <label class="fx">Brightness<input type="range" id="fxB" min="40" max="170" value="100"><output id="fxBv">100%</output></label>
    <label class="fx">Contrast<input type="range" id="fxC" min="50" max="150" value="100"><output id="fxCv">100%</output></label>
    <label class="fx">Saturation<input type="range" id="fxS" min="0" max="200" value="100"><output id="fxSv">100%</output></label>
    <button class="reset" id="fxReset">Reset picture</button>
  </div>

  <div class="err" id="err">
    <h3>Playback Error</h3>
    <p id="errMsg">Could not connect to stream.</p>
    <button class="btn" id="errRetry">Try Again</button>
  </div>
</div>

<script>
(() => {
"use strict";
const CFG = __CONFIG__;
const $ = s => document.querySelector(s);
const esc = s => String(s || "").replace(/[&<>"']/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const encPath = p => p.split("/").map(encodeURIComponent).join("/");
const clamp = (v, min, max) => Math.min(Math.max(v, min), max);
const sid = Math.random().toString(36).slice(2) + Date.now().toString(36);
const q = new URLSearchParams(location.search);
const v = $("#v");

const ICONS = {
  play: '<polygon points="6 4 20 12 6 20"/>',
  pause: '<rect x="6" y="4" width="4" height="16"/><rect x="14" y="4" width="4" height="16"/>',
  back10: '<path d="M3 12a9 9 0 1 0 9-9 9.75 9.75 0 0 0-6.74 2.74L3 8"/><path d="M3 3v5h5"/><path d="M9 10.2l1.2-.8V15" stroke-width="1.6"/><rect x="12.2" y="9.2" width="3.6" height="5.8" rx="1.8" stroke-width="1.6"/>',
  fwd10: '<path d="M21 12a9 9 0 1 1-9-9c2.52 0 4.85.83 6.74 2.74L21 8"/><path d="M21 3v5h-5"/><path d="M9 10.2l1.2-.8V15" stroke-width="1.6"/><rect x="12.2" y="9.2" width="3.6" height="5.8" rx="1.8" stroke-width="1.6"/>',
  back: '<path d="M19 12H5M12 19l-7-7 7-7"/>',
  volHi: '<polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"/><path d="M19.07 4.93a10 10 0 0 1 0 14.14M15.54 8.46a5 5 0 0 1 0 7.07"/>',
  volMid: '<polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"/><path d="M15.54 8.46a5 5 0 0 1 0 7.07"/>',
  volLow: '<polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"/>',
  volMute: '<polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"/><line x1="23" y1="9" x2="17" y2="15"/><line x1="17" y1="9" x2="23" y2="15"/>',
  max: '<path d="M8 3H5a2 2 0 0 0-2 2v3m18 0V5a2 2 0 0 0-2-2h-3m0 18h3a2 2 0 0 0 2-2v-3M3 16v3a2 2 0 0 0 2 2h3"/>',
  restore: '<path d="M8 3v3a2 2 0 0 1-2 2H3m18 0h-3a2 2 0 0 1-2-2V3m0 18v-3a2 2 0 0 1 2-2h3M3 16h3a2 2 0 0 1 2 2v3"/>',
  pip: '<rect x="2" y="4" width="20" height="16" rx="2"/><rect x="12" y="10" width="8" height="6" rx="1"/>',
  audio: '<path d="M9 18V5l12-2v13"/><circle cx="6" cy="18" r="3"/><circle cx="18" cy="16" r="3"/>',
  sliders: '<line x1="4" y1="21" x2="4" y2="14"/><line x1="4" y1="10" x2="4" y2="3"/><line x1="12" y1="21" x2="12" y2="12"/><line x1="12" y1="8" x2="12" y2="3"/><line x1="20" y1="21" x2="20" y2="16"/><line x1="20" y1="12" x2="20" y2="3"/><line x1="1" y1="14" x2="7" y2="14"/><line x1="9" y1="8" x2="15" y2="8"/><line x1="17" y1="16" x2="23" y2="16"/>',
  lock: '<rect x="3" y="11" width="18" height="11" rx="2"/><path d="M7 11V7a5 5 0 0 1 10 0v4"/>',
  unlock: '<rect x="3" y="11" width="18" height="11" rx="2"/><path d="M7 11V7a5 5 0 0 1 9.9-1"/>',
  chevL: '<path d="m15 18-6-6 6-6"/>', chevR: '<path d="m9 18 6-6-6-6"/>',
  bright: '<circle cx="12" cy="12" r="5"/><line x1="12" y1="1" x2="12" y2="3"/><line x1="12" y1="21" x2="12" y2="23"/><line x1="4.22" y1="4.22" x2="5.64" y2="5.64"/><line x1="18.36" y1="18.36" x2="19.78" y2="19.78"/><line x1="1" y1="12" x2="3" y2="12"/><line x1="21" y1="12" x2="23" y2="12"/><line x1="4.22" y1="19.78" x2="5.64" y2="18.36"/><line x1="18.36" y1="5.64" x2="19.78" y2="4.22"/>'
};

function setSvg(el, name, sz = 24) {
  if (!ICONS[name]) return;
  el.innerHTML = `<svg width="${sz}" height="${sz}" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">${ICONS[name]}</svg>`;
}
document.querySelectorAll("[data-i]").forEach(el => setSvg(el, el.dataset.i, el.dataset.s || 24));

// Title setup
if (CFG.isSeries) {
  $("#title").textContent = CFG.seriesTitle || CFG.title;
  const sLabel = CFG.seasonName || `Season ${CFG.season}`;
  $("#sub").textContent = `${sLabel} • Ep ${CFG.episode} • ${CFG.epTitle}`;
} else {
  $("#title").textContent = CFG.title;
  $("#sub").textContent = [CFG.year, CFG.quality].filter(Boolean).join(" • ");
}

// Next Episode button in controls
if (CFG.nextEpisode) {
  $("#bNext").hidden = false;
  $("#bNext").addEventListener("click", () => location.href = "/player/" + encPath(CFG.nextEpisode));
}

let DUR = CFG.duration || 0;
const dur = () => DUR || (isFinite(v.duration) && v.duration > 0 ? v.duration : 0);
const nowTime = () => freeze !== null ? freeze : (mode === "direct" ? v.currentTime : streamStart + (v.currentTime || 0));

function fmt(sec) {
  sec = Math.max(0, Math.floor(sec || 0));
  const h = Math.floor(sec / 3600), m = Math.floor(sec % 3600 / 60), s = sec % 60;
  return h ? `${h}:${String(m).padStart(2,"0")}:${String(s).padStart(2,"0")}` : `${m}:${String(s).padStart(2,"0")}`;
}

let mode = "hls", streamStart = 0, hls = null, seq = 0, chosenAudio = CFG.defaultAudio;
let freeze = null, scrubbing = false, scrubT = 0, showRemain = false, locked = false;
let switching = false, recoveries = 0;

/* ---------- controls visibility ---------- */
let idleTimer;
function showControls() {
  if (locked) return;
  $("#app").classList.remove("idle");
  clearTimeout(idleTimer);
  if (!v.paused) idleTimer = setTimeout(() => $("#app").classList.add("idle"), 3500);
}
["mousemove", "pointerdown", "touchstart"].forEach(ev => addEventListener(ev, showControls, { passive: true }));

function setLoading(on, text = "Loading...") {
  $("#spinT").textContent = text;
  $("#spin").classList.toggle("show", !!on);
}

function osd(text) {
  const o = $("#osd"); o.textContent = text; o.classList.add("show");
  clearTimeout(o._t); o._t = setTimeout(() => o.classList.remove("show"), 1200);
}

/* ---------- streaming engine ---------- */
async function startStream(startSec, opts = {}) {
  const mySeq = ++seq;
  switching = true;
  if (opts.msg) setLoading(true, opts.msg);
  try {
    const url = `/api/start?movie=${encodeURIComponent(CFG.path)}&sid=${sid}&seq=${mySeq}&t=${Math.floor(startSec)}${chosenAudio !== null ? `&audio=${chosenAudio}` : ""}${opts.forceHls ? "&mode=hls" : ""}`;
    const r = await fetch(url);
    if (!r.ok) throw new Error("HTTP " + r.status);
    const d = await r.json();
    if (d.status === "stale") return;
    if (d.status !== "ok") throw new Error(d.error || "Playback failed");

    mode = d.mode; streamStart = d.startTime || 0;
    $("#how").textContent = d.how ? d.how.toUpperCase() : mode.toUpperCase();

    if (hls) { hls.destroy(); hls = null; }
    if (mode === "direct") {
      v.src = d.url;
      if (startSec > 0) {
        if (v.readyState >= 1) {
          v.currentTime = startSec;
        } else {
          const onMeta = () => {
            v.removeEventListener("loadedmetadata", onMeta);
            try { v.currentTime = startSec; } catch (_) {}
          };
          v.addEventListener("loadedmetadata", onMeta, { once: true });
        }
      }
      await tryPlay();
    } else {
      if (v.canPlayType("application/vnd.apple.mpegurl")) {
        v.src = d.url;
        await tryPlay();
      } else if (typeof Hls !== "undefined" && Hls.isSupported()) {
        hls = new Hls({ manifestLoadingMaxRetry: 10, levelLoadingMaxRetry: 8, fragLoadingMaxRetry: 8, enableWorker: true });
        hls.loadSource(d.url);
        hls.attachMedia(v);
        hls.on(Hls.Events.MANIFEST_PARSED, () => tryPlay());
        hls.on(Hls.Events.ERROR, (e, data) => { if (data.fatal) handleFatal(); });
      }
    }
  } catch (err) {
    console.error("Stream error:", err);
    $("#errMsg").textContent = err.message || "Failed to start stream.";
    $("#err").classList.add("show");
  } finally {
    switching = false;
    setLoading(false);
  }
}

function handleFatal() {
  if (recoveries++ < 3) {
    startStream(nowTime(), { msg: "Reconnecting stream...", forceHls: true });
  } else {
    $("#errMsg").textContent = "Stream connection lost.";
    $("#err").classList.add("show");
  }
}

async function tryPlay() {
  try {
    await v.play();
    setSvg($("#bPlay span"), "pause", 28);
    setSvg($("#big span"), "pause", 34);
  } catch (e) {
    v.muted = true;
    v.play().then(() => toast("Muted playback (tap to unmute)")).catch(() => {});
  }
}

function togglePlay() {
  if (locked) return;
  if (v.paused) {
    v.play();
    setSvg($("#bPlay span"), "pause", 28);
    setSvg($("#big span"), "pause", 34);
  } else {
    v.pause();
    setSvg($("#bPlay span"), "play", 28);
    setSvg($("#big span"), "play", 34);
  }
  $("#big").classList.add("show");
  setTimeout(() => $("#big").classList.remove("show"), 350);
}
$("#bPlay").addEventListener("click", togglePlay);
$("#big").addEventListener("click", togglePlay);

/* ---------- timeline & progress ---------- */
function tick() {
  const d = dur(), t = nowTime();
  if (d > 0) {
    const pct = clamp((t / d) * 100, 0, 100);
    if (!scrubbing) {
      $("#prog").style.width = pct + "%";
      $("#knob").style.left = pct + "%";
      $("#mini").style.width = pct + "%";
      $("#tCur").textContent = fmt(t);
    }
    $("#tTot").textContent = showRemain ? `-${fmt(Math.max(0, d - t))}` : fmt(d);
  }
  // Buffer bar
  if (v.buffered && v.buffered.length > 0 && d > 0) {
    const bEnd = mode === "direct" ? v.buffered.end(v.buffered.length - 1) : streamStart + v.buffered.end(v.buffered.length - 1);
    $("#buf").style.width = clamp((bEnd / d) * 100, 0, 100) + "%";
  }

  // Next Episode auto-prompt
  checkNextEpisodePrompt(t, d);
}
v.addEventListener("timeupdate", tick);
v.addEventListener("progress", tick);
v.addEventListener("error", () => {
  if (mode === "direct" && recoveries++ < 2) {
    console.warn("Direct play failed, falling back to HLS stream...");
    startStream(nowTime(), { msg: "Optimizing stream for device...", forceHls: true });
  }
});
v.addEventListener("durationchange", () => {
  if ((!DUR || !isFinite(DUR)) && isFinite(v.duration) && v.duration > 0) {
    DUR = v.duration;
    tick();
  }
});
v.addEventListener("loadedmetadata", () => {
  if ((!DUR || !isFinite(DUR)) && isFinite(v.duration) && v.duration > 0) {
    DUR = v.duration;
    tick();
  }
});

$("#time").addEventListener("click", () => {
  showRemain = !showRemain;
  tick();
  osd(showRemain ? "Remaining time" : "Total duration");
});

/* ---------- next episode countdown ---------- */
let nextDismissed = false;
let nextTimer = null;
let nextSecs = 5;

function checkNextEpisodePrompt(cur, total) {
  if (!CFG.nextEpisode || nextDismissed || total < 60) return;
  if (cur >= total - 18) {
    if (!$("#nextCard").classList.contains("show")) {
      showNextCard();
    }
  }
}

function showNextCard() {
  $("#nextCard").classList.add("show");
  $("#nextTitle").textContent = "Auto-playing next episode";
  nextSecs = 5;
  $("#nextLabel").textContent = `Next Episode in ${nextSecs}s`;
  clearInterval(nextTimer);
  nextTimer = setInterval(() => {
    nextSecs--;
    if (nextSecs <= 0) {
      clearInterval(nextTimer);
      location.href = "/player/" + encPath(CFG.nextEpisode);
    } else {
      $("#nextLabel").textContent = `Next Episode in ${nextSecs}s`;
    }
  }, 1000);
}

$("#btnPlayNext").addEventListener("click", () => {
  if (CFG.nextEpisode) location.href = "/player/" + encPath(CFG.nextEpisode);
});
$("#btnCancelNext").addEventListener("click", () => {
  nextDismissed = true;
  clearInterval(nextTimer);
  $("#nextCard").classList.remove("show");
});

/* ---------- seeking & scrubbing ---------- */
function locallySeekable(t) {
  if (mode === "direct") return true;
  const lt = t - streamStart; if (lt < 0) return false;
  const s = v.seekable;
  for (let i = 0; s && i < s.length; i++) if (lt >= s.start(i) - .1 && lt <= s.end(i) - 1) return true;
  return false;
}

function seekTo(t) {
  if (locked) return;
  const d = dur();
  t = clamp(t, 0, d > 1 ? d - .5 : 1e9);
  if (locallySeekable(t)) {
    v.currentTime = mode === "direct" ? t : t - streamStart;
    freeze = null;
    tick();
  } else {
    startStream(t, { msg: `Seeking to ${fmt(t)}...` });
  }
}

function skip(sec) {
  if (locked) return;
  const target = clamp(nowTime() + sec, 0, dur() > 0 ? dur() - .5 : 1e9);
  const el = sec < 0 ? $("#ripL") : $("#ripR");
  const tx = sec < 0 ? $("#ripLt") : $("#ripRt");
  tx.textContent = `${sec > 0 ? "+" : ""}${sec}s`;
  el.classList.add("show");
  setTimeout(() => el.classList.remove("show"), 550);
  seekTo(target);
}
$("#bBack").addEventListener("click", () => skip(-10));
$("#bFwd").addEventListener("click", () => skip(10));

const tl = $("#tl");
function scrubAt(clientX) {
  const r = tl.getBoundingClientRect(), f = clamp((clientX - r.left) / r.width, 0, 1), d = dur();
  scrubT = f * d;
  $("#tip").style.left = clamp(clientX - r.left, 28, r.width - 28) + "px";
  $("#tip").textContent = fmt(scrubT);
  $("#tip").style.opacity = "1";
  if (scrubbing) {
    $("#prog").style.width = (f * 100) + "%";
    $("#knob").style.left = (f * 100) + "%";
    $("#mini").style.width = (f * 100) + "%";
    $("#tCur").textContent = fmt(scrubT);
  }
}

tl.addEventListener("pointerdown", e => {
  if (locked) return;
  e.preventDefault();
  scrubbing = true;
  tl.classList.add("drag");
  try { tl.setPointerCapture(e.pointerId); } catch (_) {}
  scrubAt(e.clientX);
});
tl.addEventListener("pointermove", e => {
  if (scrubbing) {
    e.preventDefault();
    scrubAt(e.clientX);
  } else if (e.pointerType === "mouse") {
    scrubAt(e.clientX);
  }
});
tl.addEventListener("pointerup", e => {
  if (!scrubbing) return;
  scrubbing = false;
  tl.classList.remove("drag");
  try { tl.releasePointerCapture(e.pointerId); } catch (_) {}
  $("#tip").style.opacity = "0";
  seekTo(scrubT);
  showControls();
});
tl.addEventListener("pointercancel", e => {
  if (!scrubbing) return;
  scrubbing = false;
  tl.classList.remove("drag");
  try { tl.releasePointerCapture(e.pointerId); } catch (_) {}
  $("#tip").style.opacity = "0";
  seekTo(scrubT);
});
tl.addEventListener("pointerleave", () => { if (!scrubbing) $("#tip").style.opacity = "0"; });

// Dedicated touch events for iOS / iPadOS Safari gesture reliability
tl.addEventListener("touchstart", e => {
  if (locked) return;
  e.preventDefault();
  scrubbing = true;
  tl.classList.add("drag");
  if (e.touches && e.touches[0]) scrubAt(e.touches[0].clientX);
}, { passive: false });

tl.addEventListener("touchmove", e => {
  if (!scrubbing) return;
  e.preventDefault();
  if (e.touches && e.touches[0]) scrubAt(e.touches[0].clientX);
}, { passive: false });

tl.addEventListener("touchend", e => {
  if (!scrubbing) return;
  e.preventDefault();
  scrubbing = false;
  tl.classList.remove("drag");
  $("#tip").style.opacity = "0";
  seekTo(scrubT);
  showControls();
}, { passive: false });

/* ---------- volume & boost ---------- */
let vol = 1.0, muted = false;
function setVolume(val) {
  vol = clamp(val, 0, 1);
  v.volume = vol;
  $("#vol").value = vol;
  $("#vol").style.setProperty("--p", (vol * 100) + "%");
  const icName = vol === 0 || muted ? "volMute" : (vol < 0.5 ? "volLow" : "volHi");
  setSvg($("#volIc"), icName, 22);
}
$("#vol").addEventListener("input", e => setVolume(parseFloat(e.target.value)));
$("#bMute").addEventListener("click", () => {
  muted = !muted;
  v.muted = muted;
  setVolume(muted ? 0 : vol || 1);
});

/* ---------- gestures (iPad & touch) ---------- */
let touchY = 0;
$("#gest").addEventListener("touchstart", e => {
  if (e.touches.length === 1) touchY = e.touches[0].clientY;
}, { passive: true });
$("#gest").addEventListener("touchmove", e => {
  if (e.touches.length === 1 && !locked) {
    const diff = touchY - e.touches[0].clientY;
    touchY = e.touches[0].clientY;
    setVolume(vol + (diff / 300));
  }
}, { passive: true });

let lastTap = 0;
$("#gest").addEventListener("click", () => {
  const now = Date.now();
  if (now - lastTap < 300) { togglePlay(); }
  else { showControls(); }
  lastTap = now;
});

/* ---------- popovers & settings ---------- */
const pops = ["popAudio", "popSpeed", "popPic"];
function closeAllPops() { pops.forEach(id => $("#" + id).classList.remove("open")); }

$("#bSpeed").addEventListener("click", e => {
  e.stopPropagation();
  const open = $("#popSpeed").classList.contains("open");
  closeAllPops();
  if (!open) $("#popSpeed").classList.add("open");
});

const speeds = [0.5, 0.75, 1.0, 1.25, 1.5, 2.0];
$("#speedList").innerHTML = speeds.map(s => `<button class="item ${s === 1 ? "on" : ""}" data-sp="${s}">${s}x</button>`).join("");
$("#speedList").addEventListener("click", e => {
  const b = e.target.closest("[data-sp]");
  if (b) {
    const sp = parseFloat(b.dataset.sp);
    v.playbackRate = sp;
    $("#bSpeed").textContent = `${sp}x`;
    document.querySelectorAll("#speedList .item").forEach(it => it.classList.toggle("on", parseFloat(it.dataset.sp) === sp));
    closeAllPops();
    osd(`Speed: ${sp}x`);
  }
});

if (CFG.audio && CFG.audio.length > 1) {
  $("#bAudio").hidden = false;
  $("#audioList").innerHTML = CFG.audio.map(a => `<button class="item ${a.index === chosenAudio ? "on" : ""}" data-a="${a.index}">${esc(a.label)}</button>`).join("");
  $("#audioList").addEventListener("click", e => {
    const b = e.target.closest("[data-a]");
    if (b) {
      chosenAudio = parseInt(b.dataset.a, 10);
      document.querySelectorAll("#audioList .item").forEach(it => it.classList.toggle("on", parseInt(it.dataset.a, 10) === chosenAudio));
      closeAllPops();
      startStream(nowTime(), { msg: "Switching audio track..." });
    }
  });
  $("#bAudio").addEventListener("click", e => {
    e.stopPropagation();
    const open = $("#popAudio").classList.contains("open");
    closeAllPops();
    if (!open) $("#popAudio").classList.add("open");
  });
}

$("#bPic").addEventListener("click", e => {
  e.stopPropagation();
  const open = $("#popPic").classList.contains("open");
  closeAllPops();
  if (!open) $("#popPic").classList.add("open");
});

document.addEventListener("click", e => {
  if (!e.target.closest(".pop") && !e.target.closest(".cb")) closeAllPops();
});

// Fullscreen & Lock
$("#bFs").addEventListener("click", () => {
  if (v.webkitEnterFullscreen) v.webkitEnterFullscreen();
  else if (!document.fullscreenElement) $("#app").requestFullscreen().catch(() => {});
  else document.exitFullscreen().catch(() => {});
});

$("#bLock").addEventListener("click", () => {
  locked = true;
  $("#app").classList.add("idle");
  $("#lockPill").classList.add("on");
  osd("Controls locked");
});
$("#lockPill").addEventListener("click", () => {
  locked = false;
  $("#lockPill").classList.remove("on");
  showControls();
  osd("Controls unlocked");
});

/* ---------- progress reporting ---------- */
function postProgress(ended = false) {
  const t = ended ? dur() : nowTime(), d = dur();
  if (d > 0 && (ended || t > 5)) {
    const body = JSON.stringify({ path: CFG.path, pos: Math.floor(t), dur: Math.floor(d) });
    if (navigator.sendBeacon) navigator.sendBeacon("/api/progress", body);
    else fetch("/api/progress", { method: "POST", body, keepalive: true }).catch(() => {});
  }
}
setInterval(() => { if (!v.paused) postProgress(); }, 5000);
v.addEventListener("ended", () => {
  postProgress(true);
  if (CFG.nextEpisode) location.href = "/player/" + encPath(CFG.nextEpisode);
});
addEventListener("pagehide", () => {
  postProgress();
  fetch("/api/stop", { method: "POST", body: JSON.stringify({ sid }), keepalive: true }).catch(() => {});
});

/* ---------- start playback ---------- */
let startAt = q.has("t") ? parseFloat(q.get("t")) || 0 : (CFG.resume || 0);
if (startAt < 10 || (DUR && startAt > DUR - 20)) startAt = 0;
startStream(startAt, { play: true });
})();
</script>
</body>
</html>
"""


if __name__ == "__main__":
    main()