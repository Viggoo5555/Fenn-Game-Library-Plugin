"""Game Library for Fenn: your Steam and Epic Games (found automatically) and the
games you add yourself, like a modded copy, in one library with their pictures.
Play with one click, see how long you've played each one and in total, sort the
list, see and start Steam updates, rename or remove the ones you added, and give
them a picture.

Click the tile to open it. Drop a game's .exe or shortcut on the page, or
press +, to add one."""

import base64
import colorsys
import difflib
import glob
import http.client
import json
import os
import queue
import re
import shutil
import subprocess
import threading
import time
import urllib.parse
import urllib.request
import zlib

import fenn

app = fenn.Plugin()

HERE = os.path.dirname(os.path.abspath(__file__))
NO_WINDOW = 0x08000000
UA = "Game-Library-for-Fenn"
GAME_FILES = (".exe", ".lnk", ".url", ".bat")
IMAGE_FILES = (".png", ".jpg", ".jpeg", ".bmp")
NET_ERRORS = (OSError, ValueError, http.client.HTTPException)
# Things Steam installs that aren't games
NOT_GAMES = ("steamworks common", "steam linux runtime", "redistributable", "proton ")
TRACK_EVERY = 20  # seconds between looks at which games are running

# the sort button cycles through these: (id, what the tooltip says, icon)
SORTS = [("recent", "recently played", "clock-counter-clockwise"),
         ("name", "name A-Z", "sort-ascending"),
         ("hours", "most hours played", "hourglass"),
         ("size", "size on disk", "hard-drives")]
TABS = ["All", "Steam", "Epic", "Added", "Hidden"]
TAB_KIND = {1: "steam", 2: "epic", 3: "custom"}  # the other tabs aren't one kind

COVERS = os.path.join(app.data_dir, "covers")  # pictures downloaded or copied here
os.makedirs(COVERS, exist_ok=True)

data = app.load("library", {})
if not isinstance(data, dict):
    data = {}
custom = data.get("custom", [])       # games you added: {id, name, path, played, cover}
hidden = set(data.get("hidden", []))  # Steam and Epic games you hid
mode = data.get("mode", "grid")       # "grid" (pictures) or "list"
sort_mode = data.get("sort", "recent")
if sort_mode not in [s[0] for s in SORTS]:
    sort_mode = "recent"
tracked = data.get("tracked", {})     # game id -> seconds we saw it running
before = data.get("before", {})       # game id -> seconds you said you played before that
seen = data.get("seen", {})           # game id -> when we last saw it running

steam_games = []  # found in Steam's own files, see scan_steam()
epic_games = []   # found in Epic's own files, see scan_epic()
steam_root = None
steam_minutes = {}     # appid -> minutes Steam itself counted (from its localconfig.vdf)
playtime_stamp = None  # which localconfig.vdf (and when changed) steam_minutes came from
epic_dir = None        # Epic's Manifests folder
epic_cat = {}          # (namespace, id) and id -> Epic's catalog entry (has the pictures)
epic_cat_stamp = None
epic_lock = threading.Lock()
tab = 0           # the chips: All, Steam, Epic, Added, Hidden
search = ""
view = "list"     # "list" or "edit" (the details of one game)
editing = None    # id of the game on the details page
form_name = ""    # what's typed in the name box
form_hours = ""   # what's typed in the hours box
form_hours0 = ""  # what it said when the page opened (to see if you changed it)
gen = 0           # changes whenever the boxes should be filled again
armed = 0         # when Remove was clicked once (it asks twice)
notice = ""
PAGE = 30         # games drawn at a time: the list is in pages, so it never gets heavier
page_no = 0       # which page (0 is the first)
last_scan = 0     # when the game files were last read with the page open
page_w = 640
page_sent = False

# which games are running, to count the time you play
running_now = set()
last_track = 0
fast_until = 0  # after starting a game, look every 5 seconds for a while
last_rescan = 0
last_save = 0
track_dirty = False
resolving = set()  # shortcuts (.lnk) we're looking up the real program of

# finding a picture on Steam for a game you added
q_open = False
q_text = ""
q_results = []    # [(appid, name)]
q_busy = False
q_searched = False
q_token = 0

# pictures
cover_q = queue.Queue()
wanted = set()    # pictures queued or fetched, so each is fetched once
retry_at = {}     # picture -> when a failed fetch may be tried again
fail_count = {}   # picture -> how many times it failed (waits longer each time)
last_notify = 0
covers_dirty = False


def save():
    app.save("library", {"custom": custom, "hidden": sorted(hidden), "mode": mode, "sort": sort_mode,
                         "tracked": {k: int(v) for k, v in tracked.items()},
                         "before": {k: int(v) for k, v in before.items()},
                         "seen": {k: int(v) for k, v in seen.items()}})


def read(path):
    with open(path, encoding="utf-8", errors="replace") as f:
        return f.read()


def field(text, key):
    m = re.search(r'"%s"\s+"([^"]*)"' % key, text)
    return m.group(1) if m else ""


def parse_vdf(text):
    """Steam's text format ("key" "value" and "key" { ... }) as nested dicts."""
    root = {}
    stack = [root]
    key = None
    for m in re.finditer(r'"((?:[^"\\]|\\.)*)"|([{}])', text):
        word, brace = m.groups()
        if brace == "{":
            node = {}
            if key is not None:
                stack[-1][key] = node
            stack.append(node)
            key = None
        elif brace == "}":
            if len(stack) > 1:
                stack.pop()
            key = None
        elif key is None:
            key = word
        else:
            stack[-1][key] = word
            key = None
    return root


# ---- Steam's own files

def find_steam():
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, r"Software\Valve\Steam") as key:
            path = winreg.QueryValueEx(key, "SteamPath")[0]
            if os.path.isdir(path):
                return os.path.normpath(path)
    except (ImportError, OSError):
        pass
    for path in (r"C:\Program Files (x86)\Steam", r"C:\Program Files\Steam"):
        if os.path.isdir(path):
            return path
    return None


def scan_steam():
    """Reads the installed games from Steam's appmanifest files, in every
    library folder (Steam keeps one per installed game)."""
    global steam_root, steam_games
    steam_root = find_steam()
    libraries = [steam_root] if steam_root else []
    if steam_root:
        try:
            for p in re.findall(r'"path"\s+"([^"]+)"', read(os.path.join(steam_root, "steamapps", "libraryfolders.vdf"))):
                p = os.path.normpath(p.replace("\\\\", "\\"))
                if p not in libraries:
                    libraries.append(p)
        except OSError:
            pass
    games, seen_ids = [], set()
    for lib in libraries:
        steamapps = os.path.join(lib, "steamapps")
        try:
            files = os.listdir(steamapps)
        except OSError:
            continue
        for fn in files:
            if not (fn.startswith("appmanifest_") and fn.endswith(".acf")):
                continue
            try:
                text = read(os.path.join(steamapps, fn))
            except OSError:
                continue
            appid, name = field(text, "appid"), field(text, "name")
            if not appid or not name or appid in seen_ids or any(w in name.lower() for w in NOT_GAMES):
                continue
            seen_ids.add(appid)
            installdir = field(text, "installdir")
            games.append({
                "id": "steam:" + appid, "kind": "steam", "appid": appid, "name": name,
                "path": os.path.join(steamapps, "common", installdir) if installdir else "",
                "played": int(field(text, "LastPlayed") or 0),
                "flags": int(field(text, "StateFlags") or 0),
                "size": int(field(text, "SizeOnDisk") or 0),
                "to_download": int(field(text, "BytesToDownload") or 0),
                "downloaded": int(field(text, "BytesDownloaded") or 0),
            })
    steam_games = games
    read_steam_playtime()


def find_apps(node, depth=0):
    """The "apps" sections of a localconfig.vdf (Steam spells the parents
    above them with different capitals over the years)."""
    for key, value in node.items():
        if isinstance(value, dict):
            if key.lower() == "apps":
                yield value
            elif depth < 6:
                yield from find_apps(value, depth + 1)


def read_steam_playtime():
    """Steam counts each game's minutes in the signed-in user's localconfig.vdf.
    Only re-read when that file has changed."""
    global steam_minutes, playtime_stamp
    if not steam_root:
        return
    base = os.path.join(steam_root, "userdata")
    best, best_time = None, -1
    try:
        users = os.listdir(base)
    except OSError:
        return
    for user in users:
        path = os.path.join(base, user, "config", "localconfig.vdf")
        try:
            stamp = os.path.getmtime(path)
        except OSError:
            continue
        if stamp > best_time:
            best, best_time = path, stamp
    if not best or (best, best_time) == playtime_stamp:
        return
    try:
        tree = parse_vdf(read(best))
    except OSError:
        return
    minutes = {}
    for apps in find_apps(tree):
        for appid, info in apps.items():
            if not isinstance(info, dict):
                continue
            lowered = {k.lower(): v for k, v in info.items()}
            try:
                minutes[appid] = max(minutes.get(appid, 0), int(lowered.get("playtime", 0)))
            except (TypeError, ValueError):
                pass
    steam_minutes, playtime_stamp = minutes, (best, best_time)


def steam_state(g):
    """("ok", 0), ("update", 0) when Steam has an update waiting, or
    ("updating", percent) while it downloads one."""
    f = g["flags"]
    if f & (256 | 1024 | 1048576):  # update running, started or downloading
        total = g["to_download"]
        return "updating", (round(g["downloaded"] / total * 100) if total else 0)
    if f & 2:  # update required
        return "update", 0
    return "ok", 0


def pending():
    return [g for g in steam_games if g["id"] not in hidden and steam_state(g)[0] == "update"]


# ---- Epic's own files

def find_epic_manifests():
    """Epic's launcher keeps one .item file per installed game in its Manifests folder."""
    candidates = []
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\WOW6432Node\Epic Games\EpicGamesLauncher") as key:
            candidates.append(os.path.join(winreg.QueryValueEx(key, "AppDataPath")[0], "Manifests"))
    except (ImportError, OSError):
        pass
    candidates.append(os.path.join(os.environ.get("PROGRAMDATA", r"C:\ProgramData"),
                                   "Epic", "EpicGamesLauncher", "Data", "Manifests"))
    for path in candidates:
        if os.path.isdir(path):
            return path
    return None


def scan_epic():
    global epic_dir, epic_games
    epic_dir = find_epic_manifests()
    games, ids = [], set()
    try:
        files = sorted(os.listdir(epic_dir)) if epic_dir else []
    except OSError:
        files = []
    for fn in files:
        if not fn.lower().endswith(".item"):
            continue
        try:
            item = json.loads(read(os.path.join(epic_dir, fn)))
        except (OSError, ValueError):
            continue
        if not isinstance(item, dict):
            continue
        name, appname = item.get("DisplayName") or "", item.get("AppName") or ""
        location = item.get("InstallLocation") or ""
        categories = [str(c).lower() for c in (item.get("AppCategories") or [])]
        if not name or not appname or appname in ids or item.get("bIsIncompleteInstall"):
            continue
        if item.get("MainGameAppName") and item["MainGameAppName"] != appname:  # extra content, not a game
            continue
        if categories and "games" not in categories:  # engines, tools
            continue
        if not os.path.isdir(location):
            continue
        ids.add(appname)
        games.append({
            "id": "epic:" + appname, "kind": "epic", "appname": appname, "name": name, "path": location,
            "ns": item.get("CatalogNamespace") or "", "itemid": item.get("CatalogItemId") or "",
            "exe": item.get("LaunchExecutable") or "", "thumb": item.get("VaultThumbnailUrl") or "",
            "size": int(item.get("InstallSize") or 0), "played": 0,
        })
    epic_games = games


def epic_catalog():
    """Epic's launcher caches the catalog (with each game's pictures) in a
    base64 file next to the manifests."""
    global epic_cat, epic_cat_stamp
    if not epic_dir:
        return {}
    path = os.path.join(os.path.dirname(epic_dir), "Catalog", "catcache.bin")
    with epic_lock:
        try:
            stamp = os.path.getmtime(path)
        except OSError:
            return epic_cat
        if stamp != epic_cat_stamp:
            catalog = {}
            try:
                with open(path, "rb") as f:
                    items = json.loads(base64.b64decode(f.read()))
                if isinstance(items, dict):
                    items = [v for v in items.values() if isinstance(v, dict)]
                for it in items:
                    if isinstance(it, dict) and it.get("id"):
                        catalog[(it.get("namespace"), it["id"])] = it
                        catalog.setdefault(it["id"], it)
            except (OSError, ValueError, TypeError):
                pass
            epic_cat, epic_cat_stamp = catalog, stamp
        return epic_cat


def epic_uri(g):
    q = lambda s: urllib.parse.quote(s, safe="")
    return "com.epicgames.launcher://apps/%s%%3A%s%%3A%s?action=launch&silent=true" % (q(g["ns"]), q(g["itemid"]), q(g["appname"]))


# ---- pictures

_valid = {}


def is_image(path):
    """PNG, JPG or BMP by its first bytes (remembered until the file changes)."""
    try:
        stamp = os.path.getmtime(path)
    except OSError:
        return False
    hit = _valid.get(path)
    if hit and hit[0] == stamp:
        return hit[1]
    try:
        with open(path, "rb") as f:
            head = f.read(4)
    except OSError:
        return False
    ok = head[:2] == b"\xff\xd8" or head[:4] == b"\x89PNG" or head[:2] == b"BM"
    _valid[path] = (stamp, ok)
    return ok


_dims = {}


def image_size(path):
    """(width, height) of a PNG, JPG or BMP, read from its header, or None."""
    try:
        stamp = os.path.getmtime(path)
    except OSError:
        return None
    hit = _dims.get(path)
    if hit and hit[0] == stamp:
        return hit[1]
    size = None
    try:
        with open(path, "rb") as f:
            head = f.read(26)
            if head[:4] == b"\x89PNG" and len(head) >= 24:
                size = (int.from_bytes(head[16:20], "big"), int.from_bytes(head[20:24], "big"))
            elif head[:2] == b"BM" and len(head) >= 26:
                size = (int.from_bytes(head[18:22], "little"), abs(int.from_bytes(head[22:26], "little", signed=True)))
            elif head[:2] == b"\xff\xd8":
                f.seek(2)
                while True:
                    marker = f.read(2)
                    if len(marker) < 2 or marker[0] != 0xFF:
                        break
                    if marker[1] in (0xD8, 0x01) or 0xD0 <= marker[1] <= 0xD7:
                        continue
                    length = int.from_bytes(f.read(2), "big")
                    if 0xC0 <= marker[1] <= 0xCF and marker[1] not in (0xC4, 0xC8, 0xCC):
                        block = f.read(5)
                        size = (int.from_bytes(block[3:5], "big"), int.from_bytes(block[1:3], "big"))
                        break
                    f.seek(length - 2, 1)
    except OSError:
        pass
    if size and (size[0] <= 0 or size[1] <= 0):
        size = None
    _dims[path] = (stamp, size)
    return size


def image_ext(body):
    if body[:2] == b"\xff\xd8":
        return ".jpg"
    if body[:4] == b"\x89PNG":
        return ".png"
    if body[:2] == b"BM":
        return ".bmp"
    return None


def complete(body):
    """False for a picture that was cut off half way through."""
    if body[:2] == b"\xff\xd8":
        return body.rfind(b"\xff\xd9") >= len(body) - 64
    if body[:4] == b"\x89PNG":
        return body[-8:-4] == b"IEND"
    return image_ext(body) is not None


def http_get(url, limit=3000000):
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=15) as r:
        body = r.read(limit + 1)
        if len(body) > limit:
            raise ValueError("too big")
        length = r.headers.get("Content-Length")
        if length and length.isdigit() and int(length) != len(body):
            raise OSError("cut off")
        return body


def download_image(urls, stem, limit=6000000):
    """Saves the first of the addresses that gives a whole picture as
    covers/<stem>.<jpg|png|bmp>; returns its path or None."""
    for url in urls:
        try:
            body = http_get(url, limit)
        except NET_ERRORS:
            continue
        ext = image_ext(body)
        if not ext or len(body) < 500 or not complete(body):
            continue
        dest = os.path.join(COVERS, stem + ext)
        with open(dest + ".part", "wb") as f:
            f.write(body)
        os.replace(dest + ".part", dest)
        for other in (".jpg", ".png", ".bmp"):  # no older copy in another format
            if other != ext:
                try:
                    os.remove(os.path.join(COVERS, stem + other))
                except OSError:
                    pass
        return dest
    return None


def cached_cover(stem):
    for ext in (".jpg", ".png", ".jpeg", ".bmp"):
        path = os.path.join(COVERS, stem + ext)
        if is_image(path):
            return path
    return None


def safe(name):
    return re.sub(r"[^A-Za-z0-9._-]+", "_", name)


_steam_found = {}
_steam_miss = {}


def steam_cache_image(appid):
    """Steam keeps the pictures of the games in your library on disk already
    (appcache/librarycache), so most need no download at all."""
    if not steam_root:
        return None
    path = _steam_found.get(appid)
    if path and is_image(path):
        return path
    if time.time() - _steam_miss.get(appid, 0) < 20:  # looked a moment ago
        return None
    base = os.path.join(steam_root, "appcache", "librarycache")
    for pattern in (appid + "_header.jpg", os.path.join(appid, "header.jpg"), os.path.join(appid, "*", "header.jpg")):
        for path in glob.glob(os.path.join(glob.escape(base), pattern)):
            if is_image(path):
                _steam_found[appid] = path
                return path
    _steam_miss[appid] = time.time()
    return None


def fetch_steam(appid):
    """Downloads a game's header picture from Steam's image servers."""
    urls = ["https://cdn.cloudflare.steamstatic.com/steam/apps/%s/header.jpg" % appid,
            "https://shared.fastly.steamstatic.com/store_item_assets/steam/apps/%s/header.jpg" % appid,
            "https://cdn.akamai.steamstatic.com/steam/apps/%s/header.jpg" % appid]
    if download_image(urls, appid):
        return True
    try:  # the store knows the picture's address, even for new games
        info = json.loads(http_get("https://store.steampowered.com/api/appdetails?filters=basic&appids=" + appid))
        return bool(download_image([info[appid]["data"]["header_image"]], appid))
    except NET_ERRORS + (KeyError, TypeError):
        return False


def norm(name):
    return re.sub(r"[^a-z0-9]+", "", re.sub(r"[\u2122\u00ae\u00a9]", "", name.lower()))


def steam_match(name):
    """The Steam app id of the game with (nearly) this name, or None."""
    info = json.loads(http_get("https://store.steampowered.com/api/storesearch/?l=english&cc=us&term="
                               + urllib.parse.quote(name.strip())))
    want, best, best_score = norm(name), None, 0
    for i in info.get("items", []):
        if i.get("type") != "app":
            continue
        score = difflib.SequenceMatcher(None, want, norm(i.get("name", ""))).ratio()
        if score > best_score:
            best, best_score = str(i["id"]), score
    return best if best_score >= 0.88 else None


EPIC_PICTURES = ("DieselGameBox", "OfferImageWide", "DieselStoreFrontWide", "Thumbnail")  # the wide ones


def epic_picture(item):
    """The best wide picture in an Epic catalog entry: {url, width, height}."""
    by_type = {}
    for im in item.get("keyImages") or []:
        if isinstance(im, dict) and im.get("url"):
            by_type.setdefault(im.get("type"), im)
    for t in EPIC_PICTURES:
        if t in by_type:
            return by_type[t]
    for im in by_type.values():
        if (im.get("width") or 0) > (im.get("height") or 0):
            return im
    return next(iter(by_type.values()), None)


def fetch_epic(j):
    """Epic's pictures are big (often 2560 x 1440), so first ask its image
    server for a small one; if that doesn't work, take the original."""
    stem = "epic-" + safe(j["appname"])
    urls = []
    item = epic_catalog().get((j["ns"], j["itemid"])) or epic_catalog().get(j["itemid"])
    im = epic_picture(item) if item else None
    if im:
        url, iw, ih = im["url"], im.get("width") or 0, im.get("height") or 0
        if iw > 640 and ih > 0:
            urls.append(url + ("&" if "?" in url else "?") + "h=%d&resize=1&w=640" % round(640 * ih / iw))
        urls.append(url)
    if j.get("thumb"):
        urls.append(j["thumb"])
    if download_image(urls, stem, limit=8000000):
        return True
    try:  # not in Epic's catalog: many Epic games are on Steam too
        appid = steam_match(j["name"])
    except NET_ERRORS + (KeyError, TypeError):
        return False
    return bool(appid) and bool(download_image(
        ["https://cdn.cloudflare.steamstatic.com/steam/apps/%s/header.jpg" % appid,
         "https://shared.fastly.steamstatic.com/store_item_assets/steam/apps/%s/header.jpg" % appid], stem))


def fetch_auto(j):
    """A game you added and that has no picture: look for one by its name."""
    try:
        appid = steam_match(j["name"])
    except NET_ERRORS + (KeyError, TypeError):
        return False
    if appid:
        app._inbox.put({"type": "auto_cover", "id": j["id"], "appid": appid})
    return bool(appid)


def want(key, kind, payload):
    """Queues a download, once (or again later after it failed, waiting longer
    each time, say because the network wasn't up yet when Windows had just started)."""
    if key in wanted and not (key in retry_at and time.time() >= retry_at[key]):
        return None
    wanted.add(key)
    retry_at.pop(key, None)
    cover_q.put((key, kind, payload))
    return None


def cover_worker():
    global last_notify, covers_dirty
    jobs = {"steam": fetch_steam, "epic": fetch_epic, "auto": fetch_auto}
    while True:
        key, kind, payload = cover_q.get()
        try:
            ok = jobs[kind](payload)
        except Exception:  # one bad picture must not stop the others
            ok = False
        if ok:
            fail_count.pop(key, None)
            if kind != "auto":
                covers_dirty = True
                if time.time() - last_notify > 0.7 or cover_q.empty():
                    last_notify = time.time()
                    app._inbox.put({"type": "cover"})
        else:
            n = fail_count[key] = fail_count.get(key, 0) + 1
            retry_at[key] = time.time() + min(60 * 2 ** (n - 1), 3600)


for _ in range(4):
    threading.Thread(target=cover_worker, daemon=True).start()


def custom_entry(gid):
    for c in custom:
        if c["id"] == gid:
            return c
    return {}


def steam_picture(appid):
    path = steam_cache_image(appid) or cached_cover(appid)
    if not path:
        want("steam:" + appid, "steam", appid)
    return path


def cover_for(g):
    """The picture file for a game, or None (a download is then started)."""
    if g["kind"] == "steam":
        return steam_picture(g["appid"])
    if g["kind"] == "epic":
        path = cached_cover("epic-" + safe(g["appname"]))
        if not path:
            want("epic:" + g["appname"], "epic", g)
        return path
    cover = custom_entry(g["id"]).get("cover") or {}
    if cover.get("file"):
        return cover["file"] if os.path.isfile(cover["file"]) else None
    if cover.get("appid"):
        return steam_picture(cover["appid"])
    if not cover.get("none"):  # never had one: look for it by name
        want("auto:" + g["id"], "auto", {"id": g["id"], "name": g["name"]})
    return None


def placeholder(name, w, h):
    """Until there's a picture: a colored panel (one color per game) with its
    initials, so the games still look different from each other."""
    r, g, b = colorsys.hsv_to_rgb((zlib.crc32(name.encode("utf-8")) % 360) / 360.0, 0.45, 0.5)
    color = "#%02X%02X%02X" % (int(r * 255), int(g * 255), int(b * 255))
    initials = "".join(x[0] for x in re.split(r"\W+", name) if x)[:2].upper() or "?"
    return fenn.canvas(h, [fenn.rect(0, 0, w, h, fill=color, radius=8),
                           fenn.label(w / 2, h / 2, initials, size=h * 0.38, color="#FFFFFF", anchor="center", bold=True)],
                       width=w)


_pic_cache = {}  # (game id, width) -> (when, node): a real picture is reused for 30 seconds


def picture(g, w):
    hit = _pic_cache.get((g["id"], w))
    if hit and time.time() - hit[0] < 30:
        return hit[1]
    node, real = _picture(g, w)
    if real:
        _pic_cache[(g["id"], w)] = (time.time(), node)
    return node


def _picture(g, w):
    """The game's picture in a w x (w * 215 / 460) box (Steam's header size).
    A picture of another shape is shrunk to fit and centered, not stretched."""
    h = int(w * 215 / 460)
    path = cover_for(g)
    if not path:
        return placeholder(g["name"], w, h), False
    iw, ih = w, h
    dims = image_size(path)
    # a picture of nearly the same shape (Epic's 16:9 next to Steam's wider one) fills the
    # whole box, so every game's picture is exactly the same size; a very different
    # shape (a tall poster, a square icon) is shrunk to fit and centered, not stretched
    if dims and not 0.75 <= (dims[0] / dims[1]) / (w / h) <= 1.33:
        scale = min(w / dims[0], h / dims[1])
        iw, ih = max(1, int(dims[0] * scale)), max(1, int(dims[1] * scale))
    node = fenn.image(path=path, width=iw, height=ih, rounding=8)
    if w - iw >= 2:
        left = (w - iw) // 2
        node = fenn.row([fenn.spacer(left), node, fenn.spacer(w - iw - left)], gap=0, align="center")
    if h - ih >= 2:
        top = (h - ih) // 2
        node = fenn.column([fenn.spacer(top), node, fenn.spacer(h - ih - top)], gap=0)
    return node, True


# ---- time played

def seconds_played(g):
    mine = tracked.get(g["id"], 0)
    if g["kind"] == "steam":  # Steam's own count, unless ours is ahead (Steam updates its file late)
        return max(steam_minutes.get(g["appid"], 0) * 60, mine)
    return max(0, mine + before.get(g["id"], 0))


def fmt_time(sec):
    if sec < 60:
        return ""
    if sec < 3600:
        return "%d min" % (sec // 60)
    hours = sec / 3600.0
    return "%.1f h" % hours if hours < 100 else "{:,} h".format(int(round(hours)))


def hours_number(sec):
    return "%.1f" % (sec / 3600.0) if sec >= 60 else "0"


def running_exes():
    return {p for _, p in running_procs()}


def running_procs():
    """(pid, full path) of the programs that are running (Windows)."""
    try:
        import ctypes
        from ctypes import wintypes
        k32 = ctypes.WinDLL("kernel32", use_last_error=True)
        psapi = ctypes.WinDLL("psapi", use_last_error=True)
        k32.OpenProcess.restype = wintypes.HANDLE
        k32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
        k32.QueryFullProcessImageNameW.restype = wintypes.BOOL
        k32.QueryFullProcessImageNameW.argtypes = [wintypes.HANDLE, wintypes.DWORD, wintypes.LPWSTR,
                                                   ctypes.POINTER(wintypes.DWORD)]
        k32.CloseHandle.argtypes = [wintypes.HANDLE]
        pids = (wintypes.DWORD * 4096)()
        got = wintypes.DWORD()
        if not psapi.EnumProcesses(pids, ctypes.sizeof(pids), ctypes.byref(got)):
            return []
        buf = ctypes.create_unicode_buffer(1024)
        out = []
        for pid in pids[:got.value // ctypes.sizeof(wintypes.DWORD)]:
            handle = k32.OpenProcess(0x1000, False, pid) if pid else None  # query limited information
            if not handle:
                continue
            try:
                size = wintypes.DWORD(len(buf))
                if k32.QueryFullProcessImageNameW(handle, 0, buf, ctypes.byref(size)):
                    out.append((int(pid), os.path.normcase(buf.value)))
            finally:
                k32.CloseHandle(handle)
        return out
    except Exception:
        return []


GENERIC_FOLDERS = ("desktop", "downloads", "documents", "windows", "system32", "program files",
                   "program files (x86)", "programdata", "users", "appdata", "temp")


def generic_folder(path):
    """A folder that holds all sorts of things, which says nothing about one game."""
    parts = [p for p in re.split(r"[\\/]+", os.path.splitdrive(os.path.normpath(path))[1]) if p]
    return len(parts) < 2 or parts[-1].lower() in GENERIC_FOLDERS


def lower_path(path):
    return os.path.normcase(os.path.normpath(path))


def run_targets(g):
    """(programs, folders) that show this game is running: any program from
    inside its folder counts, since many games start from a launcher."""
    if g["kind"] != "custom":
        return [], ([lower_path(g["path"]) + os.sep] if g["path"] else [])
    path, ext = g["path"], os.path.splitext(g["path"])[1].lower()
    exes = []
    if ext == ".exe":
        exes.append(lower_path(path))
    elif ext == ".lnk":
        path = custom_entry(g["id"]).get("target") or ""  # looked up by resolve_targets
        if path:
            exes.append(lower_path(path))
    folders = []
    folder = os.path.dirname(path) if path else ""
    if folder and ext in (".exe", ".bat", ".lnk") and not generic_folder(folder):
        folders.append(lower_path(folder) + os.sep)
    return exes, folders


def is_running(g, procs):
    exes, folders = run_targets(g)
    if not exes and not folders:
        return False
    for p in procs:
        if p in exes or any(p.startswith(f) for f in folders):
            return True
    return False


def track():
    """Looks which games are running and counts the time. True when the page
    should be drawn again."""
    global last_track, last_rescan, last_save, running_now, track_dirty
    now = time.time()
    if now - last_track < (5 if now < fast_until else TRACK_EVERY):
        return False
    delta = min(now - last_track, TRACK_EVERY * 3) if last_track else 0  # not the time the PC slept
    last_track = now
    if now - last_rescan > 300 and not app.page_open:  # (with the page open, tick() rescans)
        last_rescan = now
        scan_steam()
        scan_epic()
    procs = running_exes()
    playing = set()
    if procs:
        playing = {g["id"] for g in every_game() if is_running(g, procs)}
    for gid in playing:
        tracked[gid] = tracked.get(gid, 0) + delta
        seen[gid] = int(now)
        track_dirty = True
    changed = playing != running_now
    running_now = playing
    if track_dirty and (changed or now - last_save >= 60):
        last_save, track_dirty = now, False
        save()
    return changed or (bool(playing) and app.page_open and view == "list")


def resolve_targets():
    """Finds the program a shortcut (.lnk) you added points to, so we can tell
    when it runs."""
    for c in custom:
        if c["path"].lower().endswith(".lnk") and "target" not in c and c["id"] not in resolving:
            resolving.add(c["id"])
            threading.Thread(target=lookup_target, args=(c["id"], c["path"]), daemon=True).start()


def lookup_target(gid, path):
    target = ""
    try:
        script = ("[Console]::OutputEncoding=[System.Text.Encoding]::UTF8;"
                  "(New-Object -ComObject WScript.Shell).CreateShortcut($env:GL_LNK).TargetPath")
        out = subprocess.run(["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", script],
                             capture_output=True, creationflags=NO_WINDOW, stdin=subprocess.DEVNULL, timeout=30,
                             env=dict(os.environ, GL_LNK=path))
        target = out.stdout.decode("utf-8", "replace").strip()
    except (OSError, subprocess.TimeoutExpired):
        pass
    app._inbox.put({"type": "target", "id": gid, "target": target})


# ---- the games

def every_game():
    games = [dict(g, played=max(g.get("played", 0), int(seen.get(g["id"], 0)))) for g in steam_games + epic_games]
    for c in custom:
        games.append({"id": c["id"], "kind": "custom", "name": c["name"], "path": c["path"], "size": 0,
                      "played": max(int(c.get("played", 0)), int(seen.get(c["id"], 0)))})
    return games


def sort_key(g):
    name = g["name"].lower()
    if sort_mode == "name":
        return (name, 0)
    if sort_mode == "hours":
        return (-seconds_played(g), name)
    if sort_mode == "size":
        return (-g.get("size", 0), name)
    return (-g["played"], name)  # recently played first


def all_games():
    games = every_game()
    games.sort(key=sort_key)
    return games


def find(gid):
    for g in every_game():
        if g["id"] == gid:
            return g
    return None


def subtitle(g):
    if g["kind"] == "custom":
        parts = ["Added by you" if os.path.exists(g["path"]) else "Added by you · file missing"]
    else:
        parts = ["Steam" if g["kind"] == "steam" else "Epic Games"]
    played = fmt_time(seconds_played(g))
    if played:
        parts.append(played)
    if g.get("size"):
        parts.append("%.1f GB" % (g["size"] / 1e9))
    return " · ".join(parts)


def play(gid):
    global notice, fast_until
    g = find(gid)
    if not g:
        return
    if g["kind"] == "steam":
        steam_cmd(["-applaunch", g["appid"]])
    elif g["kind"] == "epic":
        exe = os.path.join(g["path"], g["exe"]) if g["exe"] else ""
        if g["ns"] and g["itemid"]:  # through Epic's launcher, which signs the game in
            os.startfile(epic_uri(g))
        elif os.path.isfile(exe):
            os.startfile(exe)
        else:
            notice = "Can't start " + g["name"] + ". Try it from the Epic Games Launcher."
            return
    elif os.path.exists(g["path"]):
        try:
            os.startfile(g["path"], cwd=os.path.dirname(g["path"]))  # starts it in its own folder (Python 3.10+)
        except TypeError:
            os.startfile(g["path"])
        custom_entry(gid)["played"] = int(time.time())
    else:
        notice = "Can't find " + g["path"]
        return
    seen[gid] = int(time.time())
    fast_until = time.time() + 120
    save()
    app.close_page()


def steam_cmd(args):
    """Runs Steam with these arguments, as quietly as it goes: -silent keeps its
    window away when it has to start, it's started hidden, and for a few seconds
    any Steam window (not the game's) that shows up is hidden again at once."""
    exe = os.path.join(steam_root, "steam.exe") if steam_root else ""
    if os.path.isfile(exe):
        threading.Thread(target=hide_steam_windows, daemon=True).start()  # already watching when Steam starts
        extra = {}
        if hasattr(subprocess, "STARTUPINFO"):
            info = subprocess.STARTUPINFO()
            info.dwFlags |= subprocess.STARTF_USESHOWWINDOW
            info.wShowWindow = 0  # SW_HIDE
            extra["startupinfo"] = info
        subprocess.Popen([exe, "-silent"] + args, creationflags=NO_WINDOW, stdin=subprocess.DEVNULL,
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, **extra)
    else:  # Steam's folder wasn't found: the plain steam:// address, which Windows hands to Steam
        os.startfile(args[-1] if args[-1].startswith("steam://") else "steam://rungameid/" + args[-1])


def hide_steam_windows(seconds=15):
    """Hides Steam's own windows (its main window, the verify box) for a few
    seconds, checking about 30 times a second so they never get to be seen.
    Steam hides its window like this itself when it sits in the tray."""
    try:
        import ctypes
        from ctypes import wintypes
        user32 = ctypes.WinDLL("user32", use_last_error=True)
        k32 = ctypes.WinDLL("kernel32", use_last_error=True)
        k32.OpenProcess.restype = wintypes.HANDLE
        k32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
        k32.QueryFullProcessImageNameW.argtypes = [wintypes.HANDLE, wintypes.DWORD, wintypes.LPWSTR,
                                                   ctypes.POINTER(wintypes.DWORD)]
        k32.CloseHandle.argtypes = [wintypes.HANDLE]
        root = os.path.normcase(os.path.normpath(steam_root)) + os.sep
        paths = {}  # process id -> the program's path, looked up the first time a window of it shows

        def path_of(pid):
            if pid not in paths:
                path = ""
                handle = k32.OpenProcess(0x1000, False, pid)
                if handle:
                    try:
                        buf = ctypes.create_unicode_buffer(1024)
                        size = wintypes.DWORD(len(buf))
                        if k32.QueryFullProcessImageNameW(handle, 0, buf, ctypes.byref(size)):
                            path = os.path.normcase(buf.value)
                    finally:
                        k32.CloseHandle(handle)
                paths[pid] = path
            return paths[pid]

        def each(hwnd, _):
            if user32.IsWindowVisible(hwnd):
                pid = wintypes.DWORD()
                user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
                path = path_of(pid.value)
                if path.startswith(root) and "steamapps" not in path:
                    user32.ShowWindow(hwnd, 0)  # hidden
            return True

        enum = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)(each)
        end = time.time() + seconds
        while time.time() < end:
            user32.EnumWindows(enum, 0)
            time.sleep(0.03)
    except Exception:
        pass


def stop(gid):
    """Closes the game: every program of it that is running."""
    global notice, running_now
    g = find(gid)
    if not g:
        return
    exes, folders = run_targets(g)
    pids = [pid for pid, p in running_procs() if p in exes or any(p.startswith(f) for f in folders)]
    for pid in pids:
        try:
            subprocess.run(["taskkill", "/PID", str(pid), "/T", "/F"], capture_output=True,
                           creationflags=NO_WINDOW, stdin=subprocess.DEVNULL, timeout=15)
        except (OSError, subprocess.TimeoutExpired):
            pass
    running_now = running_now - {gid}
    notice = ("Stopped " + g["name"] + ".") if pids else (g["name"] + " isn't running.")


def update(gid):
    """Steam updates games on its own; this asks it to check one now (verifying
    the files also downloads any update that's waiting)."""
    global notice
    g = find(gid)
    if g and g["kind"] == "steam":
        steam_cmd(["steam://validate/" + g["appid"]])
        notice = "Asked Steam to update " + g["name"] + ". Steam's Downloads page shows how it goes."


def update_all():
    global notice
    ids = [g["appid"] for g in pending()]

    def work():
        for appid in ids:
            steam_cmd(["steam://validate/" + appid])
            time.sleep(1.5)

    threading.Thread(target=work, daemon=True).start()
    notice = "Asked Steam to update %d game%s. Steam's Downloads page shows how it goes." % (len(ids), "" if len(ids) == 1 else "s")


def show_folder(g):
    if not g:
        return
    if g["kind"] == "custom" and os.path.exists(g["path"]):
        subprocess.Popen('explorer /select,"%s"' % os.path.normpath(g["path"]))
    elif os.path.isdir(g["path"]):
        os.startfile(g["path"])


def add_game(path):
    """Adds a game file named after the file; returns its id."""
    path = os.path.normpath(path)
    for c in custom:
        if os.path.normcase(c["path"]) == os.path.normcase(path):
            return c["id"]
    n = max([int(c["id"].split(":")[1]) for c in custom] + [0]) + 1
    custom.append({"id": "custom:%d" % n, "name": os.path.splitext(os.path.basename(path))[0], "path": path, "played": 0})
    save()
    resolve_targets()
    return "custom:%d" % n


def open_edit(gid):
    global view, editing, form_name, form_hours, form_hours0, gen, armed, q_open, q_text, q_results, q_searched
    g = find(gid)
    if not g:
        return
    view, editing, form_name, gen, armed = "edit", gid, g["name"], gen + 1, 0
    form_hours = form_hours0 = hours_number(seconds_played(g))
    q_results, q_searched = [], False
    q_text = g["name"]
    # a game you added and that has no picture yet: look it up on Steam right away
    cover = custom_entry(gid).get("cover") or {}
    q_open = g["kind"] == "custom" and not (cover.get("file") or cover.get("appid") or cover.get("none"))
    if q_open:
        steam_search(q_text)


def save_name():
    global view
    g = find(editing)
    name = form_name.strip()
    for c in custom:
        if c["id"] == editing and name:
            c["name"] = name
    if g and g["kind"] != "steam" and form_hours.strip() != form_hours0:
        try:  # what you type is the total; keep the time we counted and make up the rest
            total = float(re.sub(r"[^0-9.]", "", form_hours.replace(",", ".")) or "0")
            before[editing] = int(total * 3600) - int(tracked.get(editing, 0))
        except ValueError:
            pass
    save()
    view = "list"


def set_picture(cover):
    """cover: {"appid": ...} (a game's picture on Steam) or {"file": ...} (your own)."""
    _pic_cache.clear()
    custom_entry(editing)["cover"] = cover
    save()


def set_own_picture(path):
    ext = os.path.splitext(path)[1].lower()
    if ext in IMAGE_FILES and custom_entry(editing):
        dest = os.path.join(COVERS, editing.replace(":", "-") + ext)
        shutil.copyfile(path, dest)  # a copy, so it still works if you move the original
        _dims.pop(dest, None)
        set_picture({"file": dest})


def steam_search(term):
    """Asks Steam's store which game you mean (a few best matches)."""
    global q_busy, q_token
    term = term.strip()
    if not term:
        return
    q_token += 1
    token, q_busy = q_token, True

    def work():
        items = []
        try:
            info = json.loads(http_get("https://store.steampowered.com/api/storesearch/?l=english&cc=us&term="
                                       + urllib.parse.quote(term)))
            items = [(str(i["id"]), i["name"]) for i in info.get("items", []) if i.get("type") == "app"][:6]
        except NET_ERRORS + (KeyError, TypeError):
            pass
        app._inbox.put({"type": "found", "token": token, "items": items})

    threading.Thread(target=work, daemon=True).start()


def pick_file(kind):
    """Windows' file picker, in a thread so Fenn stays responsive."""
    start = os.path.join(steam_root, "steamapps", "common") if steam_root and kind == "game" else ""

    def work():
        path = ""
        try:
            out = subprocess.run(["powershell", "-NoProfile", "-STA", "-ExecutionPolicy", "Bypass", "-File",
                                  os.path.join(HERE, "pick_file.ps1"), "-Start", start, "-Kind", kind],
                                 capture_output=True, creationflags=NO_WINDOW, stdin=subprocess.DEVNULL, timeout=600)
            path = out.stdout.decode("utf-8", "replace").strip()
        except (OSError, subprocess.TimeoutExpired):
            pass
        app._inbox.put({"type": "picked", "kind": kind, "path": path})

    threading.Thread(target=work, daemon=True).start()


def prefetch(games=None):
    """Gets pictures ready on disk in the background (from Steam's own cache or
    downloaded): by default the first two pages, and while you browse, the next
    page. Only files are fetched; nothing is drawn until you're on that page."""
    if games is None:
        games = all_games()[:PAGE * 2]
    for g in games:
        try:
            cover_for(g)
        except Exception:
            pass


def signature():
    return (tuple((g["id"], g["flags"], g["downloaded"]) for g in steam_games),
            tuple(g["id"] for g in epic_games), playtime_stamp)


# ---- views

def short(name, w):
    n = max(10, int(w / 7.5))
    return name if len(name) <= n else name[:n - 1].rstrip() + "…"


def grid_size():
    cols = 3 if page_w >= 600 else 2
    return cols, int((page_w - 40 - 8 * (cols - 1)) / cols - 18)  # columns, picture width


def status_info(g, state, pct):
    """(text, color name) of a game's second line."""
    played = fmt_time(seconds_played(g))
    if g["id"] in running_now:
        return "Playing now" + (" · " + played if played else ""), "green"
    if state == "update":
        return "Update available" + (" · " + played if played else ""), "orange"
    if state == "updating":
        return "Updating %d%%" % pct, "orange"
    return subtitle(g), "dim"


def status_line(g, state, pct):
    text, color = status_info(g, state, pct)
    return fenn.text(text, size="small", color=color)


def ink():
    return "#F2F3F5" if app.dark else "#1B1D21"


def neutral():
    return "#3A3D45" if app.dark else "#D5D9E0"


def edit_button(g):
    return color_button("edit:" + g["id"], None, "dots-three", neutral(), "Details")


def text_block(g, state, pct, w, h):
    """Name and status drawn at a fixed size, so every row has the same width
    and its buttons end up in the same place (Fenn sizes plain text to its content)."""
    text, color = status_info(g, state, pct)
    hexes = {"green": "#3CCB7F", "orange": "#F59F00", "dim": "#9AA0A6" if app.dark else "#5F6672"}
    return fenn.canvas(h, [fenn.label(0, h * 0.30, short(g["name"], w * 0.92), size=14, color=ink(), anchor="start", bold=True),
                           fenn.label(0, h * 0.72, short(text, w * 1.1), size=12, color=hexes.get(color, "#9AA0A6"), anchor="start")],
                       width=w)


RED, AMBER, GREY = "#E03131", "#F59F00", "#6B7280"  # Stop, Update, and the track of an update's progress
BTN_H, BTN_W, BTN_ICON_W, BTN_R = 26, 74, 30, 7  # every state of the main button has exactly this size


def ink_for(fill):
    """White or near-black text, whichever reads better on this color."""
    try:
        r, g, b = (int(fill[i:i + 2], 16) for i in (1, 3, 5))
    except (ValueError, IndexError):
        return "#FFFFFF"
    return "#1A1A1A" if (0.299 * r + 0.587 * g + 0.114 * b) > 150 else "#FFFFFF"


def color_button(id, label, glyph_name, fill, tooltip, progress=None, track=None):
    """A button of our own color (Fenn's buttons only have its accent color), drawn
    on a canvas that sends a click with this id. label None: icon only.
    progress 0-100 fills the button left to right over `track`."""
    h = BTN_H
    w = BTN_W if label else BTN_ICON_W
    ink = ink_for(track if progress is not None else fill)
    if progress is not None:
        shapes = [fenn.rect(0, 0, w, h, fill=track, radius=BTN_R)]
        if progress > 0:
            shapes.append(fenn.rect(0, 0, max(14, w * progress / 100.0), h, fill=fill, radius=BTN_R))
    else:
        shapes = [fenn.rect(0, 0, w, h, fill=fill, radius=BTN_R)]
    if label:  # icon and text together, centered
        text_w = 6.6 * len(label)
        left = (w - (18 + text_w)) / 2
        shapes += [fenn.glyph(left + 6, h / 2, glyph_name, size=13, color=ink, fill=True),
                   fenn.label(left + 18, h / 2, label, size=12, color=ink, anchor="start", bold=True)]
    else:
        shapes.append(fenn.glyph(w / 2, h / 2, glyph_name, size=15, color=ink, fill=True))
    return fenn.canvas(h, shapes, width=w, id=id, tooltip=tooltip)


def play_button(g, state, pct, labeled):
    """One button, always the same size: Play in Fenn's accent color, a red Stop
    while the game runs, an orange Update when it needs one, and while it
    updates a bar that fills as the download goes."""
    if g["id"] in running_now:
        return color_button("stop:" + g["id"], "Stop" if labeled else None, "stop", RED, "Stop")
    if state == "update":
        return color_button("update:" + g["id"], "Update" if labeled else None, "arrow-circle-down", AMBER, "Update")
    if state == "updating":
        return color_button("noop", ("Updating" if labeled else None), "arrow-circle-down", AMBER,
                            "Updating %d%%" % pct, progress=pct, track=GREY)
    return color_button("play:" + g["id"], "Play" if labeled else None, "play", app.accent, "Play")


def game_card(g, w, hidden_tab=False):
    state, pct = steam_state(g) if g["kind"] == "steam" else ("ok", 0)
    if hidden_tab:
        buttons = [color_button("unhide:" + g["id"], "Show", "eye", neutral(), "Show")]
    else:
        buttons = [play_button(g, state, pct, True), fenn.spacer(), edit_button(g)]
    return fenn.card([picture(g, w), fenn.text(short(g["name"], w), bold=True), status_line(g, state, pct),
                      fenn.row(buttons, gap=4, align="center")], padding=8, gap=4)


def game_row(g, hidden_tab=False):
    state, pct = steam_state(g) if g["kind"] == "steam" else ("ok", 0)
    if hidden_tab:
        buttons = [color_button("unhide:" + g["id"], "Show", "eye", neutral(), "Show")]
    else:
        buttons = [edit_button(g), play_button(g, state, pct, False)]
    buttons_w = sum(b["width"] for b in buttons) + 4 * (len(buttons) - 1)
    h = int(112 * 215 / 460)
    text_w = max(80, page_w - 56 - 112 - 20 - buttons_w - 6)  # what's left of the row: the same in every row
    return fenn.card([fenn.row([
        picture(g, 112),
        text_block(g, state, pct, text_w, h),
        fenn.row(buttons, gap=4, align="center"),
    ], gap=10, align="center")], padding=8)


def sort_label():
    return [s[1] for s in SORTS if s[0] == sort_mode][0]


def pager(page, pages, shown, games):
    """Which page you're on, with Previous and Next in a quiet gray (left out where there's nowhere to go)."""
    buttons = []
    if page > 0:
        buttons.append(color_button("prev", "Previous", "caret-left", neutral(), "Previous page"))
    if page < pages - 1:
        buttons.append(color_button("next", "Next", "caret-right", neutral(), "Next page"))
    return fenn.row([fenn.text("Page %d of %d" % (page + 1, pages), bold=True),
                     fenn.spacer()] + buttons, gap=8, align="center")


def list_view():
    global page_no
    q = search.strip().lower()
    games = all_games()
    if tab == 4:
        games = [g for g in games if g["id"] in hidden]
    else:
        games = [g for g in games if g["id"] not in hidden]
        if tab in TAB_KIND:
            games = [g for g in games if g["kind"] == TAB_KIND[tab]]
    games = [g for g in games if q in g["name"].lower()]
    total = sum(seconds_played(g) for g in games)
    pages = max(1, -(-len(games) // PAGE))
    page = page_no = min(page_no, pages - 1)  # (so Next past the last page can't pile up)
    shown = games[page * PAGE:(page + 1) * PAGE]
    prefetch(games[(page + 1) * PAGE:(page + 2) * PAGE])  # the next page's pictures, so they're ready

    if shown and mode == "grid":
        cols, w = grid_size()
        body = [fenn.grid(cols, [game_card(g, w, tab == 4) for g in shown], gap=8)]
    else:
        body = [game_row(g, tab == 4) for g in shown]
    if not shown:
        if q:
            line = "No games match that."
        elif tab == 4:
            line = "No hidden games."
        elif tab == 2 and not epic_dir:
            line = "The Epic Games Launcher wasn't found. Drop a game's .exe or shortcut here to add one yourself."
        elif tab == 2:
            line = "No installed Epic games found."
        elif tab == 1 and not steam_root:
            line = "Steam wasn't found. Drop a game's .exe or shortcut here, or press + to add one."
        elif not steam_root and not epic_dir and not custom:
            line = "No Steam or Epic games found. Drop a game's .exe or shortcut here, or press + to add one."
        else:
            line = "No games here yet. Drop a game's .exe or shortcut here, or press + to add one."
        body = [fenn.text(line, color="dim", wrap=True)]
    else:
        if pages > 1:
            body.append(pager(page, pages, shown, games))
        if tab in (0, 3):
            body.append(fenn.text("Drop a game's .exe or shortcut here to add it.", size="small", color="faint"))

    top = [fenn.text_input("search", search, hint="Search your games", width=page_w - 40, live=True),
           fenn.chips("tab", TABS, selected=tab)]
    if games:
        top.append(fenn.text("%s played in total · sorted by %s" % (fmt_time(total) or "0 h", sort_label()),
                             size="small", color="dim", wrap=True))
    if notice:
        top.append(fenn.text(notice, size="small", color="orange", wrap=True))
    return fenn.column(top + [fenn.column(body, gap=6, scroll=True, id="games%d%s%s%d" % (tab, mode, sort_mode, page))], gap=8)


def search_section():
    out = [fenn.row([fenn.text_input("steamq%d" % gen, q_text, hint="Search Steam by name", width=page_w - 130, live=True),
                     fenn.button("steam_search", icon="magnifying-glass", tooltip="Search Steam")], gap=6, align="center")]
    if q_busy:
        out.append(fenn.text("Searching Steam…", size="small", color="dim"))
    elif q_results:
        out.append(fenn.text("Pick the game to use its picture:", size="small", color="dim"))
        out.append(fenn.list_view([fenn.item("pick:" + i, n, subtitle="Steam", icon="steam-logo") for i, n in q_results]))
    elif q_searched:
        out.append(fenn.text("Nothing found. Try another name.", size="small", color="dim"))
    return out


def hours_box():
    return [fenn.text("Hours played", size="small", color="dim"),
            fenn.text_input("hours%d" % gen, form_hours, hint="For example 12.5", width=140, live=True)]


def edit_view():
    global view
    g = find(editing)
    if not g:
        view = "list"
        return list_view()
    parts = [picture(g, 280)]
    if g["kind"] in ("steam", "epic"):
        state, pct = steam_state(g) if g["kind"] == "steam" else ("ok", 0)
        status = subtitle(g) + {"update": " · Update available", "updating": " · Updating %d%%" % pct}.get(state, "")
        parts += [fenn.text(g["name"], size="title", bold=True, wrap=True),
                  fenn.text(status, size="small", color="dim"),
                  fenn.text(g["path"], size="small", color="faint", wrap=True)]
        hide = g["id"] in hidden
        hide_button = fenn.button(("unhide:" if hide else "hide:") + g["id"], label="Show" if hide else "Hide",
                                  icon="eye" if hide else "eye-slash")
        if g["kind"] == "steam":
            buttons = [play_button(g, state, pct, True)]
            if state != "update":  # (the main button is already Update then)
                buttons.append(fenn.button("update:" + g["id"], label="Update", icon="arrow-circle-down"))
            buttons += [fenn.button("folder:" + g["id"], label="Folder", icon="folder-open"), hide_button]
            parts += [fenn.row(buttons, gap=6),
                      fenn.text("Steam updates games on its own. Update asks it to check this one now: it verifies the "
                                "files, which also downloads any update that's waiting.", size="small", color="dim", wrap=True)]
        else:
            buttons = [fenn.button("save", label="Save", icon="check", primary=True),
                       play_button(g, "ok", 0, True),
                       fenn.button("folder:" + g["id"], label="Folder", icon="folder-open"), hide_button]
            parts += hours_box() + [
                fenn.row(buttons, gap=6),
                fenn.text("Epic doesn't keep play time on this PC, so Game Library counts it while the game runs. "
                          "If you played before that, type your total hours above and press Save.",
                          size="small", color="dim", wrap=True)]
    else:
        sure = armed and time.time() - armed < 5
        parts += [fenn.text("Name", size="small", color="dim"),
                  fenn.text_input("name%d" % gen, form_name, hint="How it shows in your library",
                                  width=page_w - 40, live=True)]
        parts += hours_box()
        parts.append(fenn.text(g["path"], size="small", color="faint", wrap=True))
        buttons = [fenn.button("save", label="Save", icon="check", primary=True),
                   play_button(g, "ok", 0, True),
                   fenn.button("folder:" + g["id"], label="Folder", icon="folder-open"),
                   fenn.button("remove", label="Click again" if sure else "Remove", icon="warning" if sure else "trash")]
        pic = [fenn.button("steam_pic", label="Find on Steam", icon="magnifying-glass"),
               fenn.button("own_pic", label="Choose image", icon="image")]
        cover = custom_entry(g["id"]).get("cover") or {}
        if cover.get("file") or cover.get("appid"):
            pic.append(fenn.button("no_pic", label="Remove picture", icon="x"))
        parts += [fenn.row(buttons, gap=6),
                  fenn.text("Remove only takes it off this list; the game's files stay where they are.",
                            size="small", color="dim", wrap=True),
                  fenn.text("Picture", size="small", color="dim"),
                  fenn.row(pic, gap=6)]
        if q_open:
            parts += search_section()
    if notice:
        parts.append(fenn.text(notice, size="small", color="orange", wrap=True))
    return fenn.column(parts, gap=8, scroll=True, id="edit")


def actions():
    if view == "edit":
        return [{"id": "back", "icon": "arrow-left", "tooltip": "Back to the library"}]
    labels = [s[1] for s in SORTS]
    following = labels[(labels.index(sort_label()) + 1) % len(labels)]
    acts = [{"id": "add", "icon": "plus", "tooltip": "Add a game (or drop its .exe here)"},
            {"id": "sort", "icon": [s[2] for s in SORTS if s[0] == sort_mode][0],
             "tooltip": "Sorted by %s. Click to sort by %s" % (sort_label(), following)},
            {"id": "mode", "icon": "list" if mode == "grid" else "squares-four",
             "tooltip": "Show as a list" if mode == "grid" else "Show with big pictures"}]
    n = len(pending())
    if n:
        acts.append({"id": "update_all", "icon": "arrow-circle-down",
                     "tooltip": "Update %d game%s" % (n, "" if n == 1 else "s")})
    return acts


def draw():
    global page_sent
    app.tile(fenn.column([fenn.icon("game-controller", size=22, tooltip="Game Library")],
                         align="center", justify="center"))
    if app.page_open or not page_sent:
        app.page(edit_view() if view == "edit" else list_view(), actions())
        page_sent = True


# ---- events

@app.on_message("event")
def on_event(msg):
    global search, tab, view, notice, armed, form_name, form_hours, q_text, q_open, mode, sort_mode, page_no
    eid, kind, value = msg.get("id", ""), msg.get("kind"), msg.get("value")
    action, _, rest = eid.partition(":")
    if eid == "search":
        search, page_no = str(value or ""), 0
    elif eid == "tab":
        tab, page_no = int(value["index"]), 0
    elif eid.startswith("name"):
        form_name = str(value or "")
        if kind != "submit":
            return
        save_name()
    elif eid.startswith("hours"):
        form_hours = str(value if value is not None else "")
        if kind != "submit":
            return
        save_name()
    elif eid.startswith("steamq"):
        q_text = str(value or "")
        if kind != "submit":
            return
        steam_search(q_text)
    else:
        notice = ""
        if action == "play":
            play(rest)
        elif action == "stop":
            stop(rest)
        elif action == "edit":
            open_edit(rest)
        elif action == "update":
            update(rest)
        elif action == "folder":
            show_folder(find(rest))
        elif action == "hide":
            hidden.add(rest)
            save()
            view = "list"
        elif action == "unhide":
            hidden.discard(rest)
            save()
        elif action == "pick":
            set_picture({"appid": rest})
            q_open = False
        elif eid == "save":
            save_name()
        elif eid == "remove":
            if armed and time.time() - armed < 5:
                custom[:] = [c for c in custom if c["id"] != editing]
                for store in (tracked, before, seen):
                    store.pop(editing, None)
                save()
                view, armed = "list", 0
            else:
                armed = time.time()
        elif eid == "steam_pic":
            q_open = True
            q_text = form_name
            steam_search(q_text)
        elif eid == "steam_search":
            steam_search(q_text)
        elif eid == "own_pic":
            pick_file("image")
        elif eid == "no_pic":
            _pic_cache.clear()
            custom_entry(editing)["cover"] = {"none": True}  # and don't look for one again
            save()
        elif eid == "add":
            pick_file("game")
        elif eid == "mode":
            mode, page_no = ("list" if mode == "grid" else "grid"), 0
            save()
        elif eid == "sort":
            names = [s[0] for s in SORTS]
            sort_mode, page_no = names[(names.index(sort_mode) + 1) % len(names)], 0
            save()
        elif eid == "next":
            page_no += 1
        elif eid == "prev":
            page_no = max(0, page_no - 1)
        elif eid == "update_all":
            update_all()
        elif eid == "back":
            view = "list"
    draw()


@app.on_message("files")
def on_files(msg):
    global notice
    notice = ""
    paths = [p for p in msg.get("paths", []) if os.path.isfile(p)]
    pics = [p for p in paths if p.lower().endswith(IMAGE_FILES)]
    if pics and view == "edit":  # a picture dropped on a game's page becomes its picture
        set_own_picture(pics[0])
    ids = [add_game(p) for p in paths if p.lower().endswith(GAME_FILES)]
    if len(ids) == 1:
        open_edit(ids[0])  # so you can name it right away
    elif ids:
        notice = "Added %d games." % len(ids)
    draw()


@app.on_message("picked")
def on_picked(msg):
    global notice
    path = msg.get("path")
    if path and os.path.isfile(path):
        notice = ""
        if msg.get("kind") == "image":
            set_own_picture(path)
        else:
            open_edit(add_game(path))
        draw()


@app.on_message("found")
def on_found(msg):
    global q_busy, q_results, q_searched
    if msg.get("token") == q_token:
        q_busy, q_results, q_searched = False, msg.get("items", []), True
        draw()


@app.on_message("auto_cover")
def on_auto_cover(msg):
    c = custom_entry(msg.get("id"))
    if c and not c.get("cover"):  # still no picture of your own
        c["cover"] = {"appid": msg["appid"]}
        save()
        draw()


@app.on_message("target")
def on_target(msg):
    c = custom_entry(msg.get("id"))
    if c:
        c["target"] = msg.get("target") or ""
        save()


@app.on_message("cover")
def on_cover(_):
    global covers_dirty
    covers_dirty = False
    if app.page_open:
        draw()


@app.on_message("layout")
def on_layout(msg):
    global page_w
    if msg.get("target") == "page":
        page_w = int(msg.get("width") or page_w)
    draw()


@app.on_message("page_open")
def on_open(_):
    global last_scan
    last_scan = time.time()
    scan_steam()
    scan_epic()
    prefetch()
    draw()


@app.on_message("hello")
def on_hello(_):
    draw()


@app.on_message("theme")
def on_theme(_):
    draw()


# ---- timers

def tick():
    global armed, covers_dirty, last_scan
    redraw = False
    if armed and time.time() - armed >= 5:
        armed = 0
        redraw = True
    if track():  # a game started or stopped
        redraw = True
    if app.page_open and view == "list":  # follow Steam's updates while the page is open
        if time.time() - last_scan >= 30:
            last_scan = time.time()
            before_scan = signature()
            scan_steam()
            scan_epic()
            if signature() != before_scan:
                prefetch()  # pictures of games that were just installed
                redraw = True
        if covers_dirty:
            covers_dirty = False
            redraw = True
    if redraw:
        draw()


if __name__ == "__main__":
    scan_steam()
    scan_epic()
    prefetch()
    resolve_targets()
    app.every(5, tick)
    draw()
    app.run()
