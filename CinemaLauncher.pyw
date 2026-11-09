"""
Cinema Streaming Server Launcher
A modern desktop app with cinematic glass UI to start, stop, and monitor the Cinema server.
"""

import json
import os
import socket
import subprocess
import sys
import threading
import time
import webbrowser
from pathlib import Path
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

BASE_DIR = Path(sys.executable).parent.resolve() if getattr(sys, "frozen", False) else Path(__file__).parent.resolve()
BUNDLE_DIR = Path(getattr(sys, "_MEIPASS", BASE_DIR))


def resolve_path(filename, subfolder=""):
    candidates = []
    if subfolder:
        candidates.append(BASE_DIR / subfolder / filename)
        candidates.append(BUNDLE_DIR / subfolder / filename)
    candidates.append(BASE_DIR / filename)
    candidates.append(BUNDLE_DIR / filename)

    for c in candidates:
        if c.exists():
            return c
    return BASE_DIR / (Path(subfolder) / filename if subfolder else filename)


SERVER_SCRIPT = resolve_path("portfilespacificforipad.py")
CONFIG_FILE = BASE_DIR / ".launcher_config.json"
ICON_FILE = resolve_path("cinema.ico", "assets")
PNG_ICON_512 = resolve_path("cinema.png", "assets")
PNG_ICON_192 = resolve_path("cinema-192.png", "assets")
PNG_ICON_32 = resolve_path("cinema-32.png", "assets")
MANIFEST_FILE = resolve_path("manifest.json", "assets")
UI_FILE = resolve_path("launcher_ui.html", "ui")


def apply_native_window_icon(icon_path, target_title="Cinema Server Launcher", max_attempts=25):
    if os.name != "nt":
        return
    try:
        import ctypes
        user32 = ctypes.windll.user32
        WM_SETICON = 0x80
        ICON_SMALL = 0
        ICON_BIG = 1
        IMAGE_ICON = 1
        LR_LOADFROMFILE = 0x0010

        hicon_big = user32.LoadImageW(None, str(icon_path), IMAGE_ICON, 48, 48, LR_LOADFROMFILE)
        hicon_small = user32.LoadImageW(None, str(icon_path), IMAGE_ICON, 16, 16, LR_LOADFROMFILE)

        if not hicon_big or not hicon_small:
            return

        for _ in range(max_attempts):
            hwnd = user32.FindWindowW(None, target_title)
            if hwnd:
                user32.SendMessageW(hwnd, WM_SETICON, ICON_BIG, hicon_big)
                user32.SendMessageW(hwnd, WM_SETICON, ICON_SMALL, hicon_small)
                break
            time.sleep(0.25)
    except Exception:
        pass


def get_local_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("10.255.255.255", 1))
        return s.getsockname()[0]
    except Exception:
        return "127.0.0.1"
    finally:
        s.close()


def load_config():
    defaults = {
        "movie_dir": r"I:\Movies",
        "port": 8000,
        "auto_start": False,
    }
    if CONFIG_FILE.exists():
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
                defaults.update(data)
        except Exception:
            pass
    return defaults


def save_config(cfg):
    try:
        with open(CONFIG_FILE, "w", encoding="utf-8") as f:
            json.dump(cfg, f, indent=2)
    except Exception:
        pass


def make_desktop_shortcut():
    desktop = Path(os.environ.get("USERPROFILE", "")) / "Desktop"
    if not desktop.exists():
        return False, "Desktop folder not found."
    lnk = desktop / "Cinema Server.lnk"

    if getattr(sys, "frozen", False):
        target_path = Path(sys.executable).resolve()
        arguments = ""
        work_dir = target_path.parent
    else:
        target_path = Path(sys.executable).with_name("pythonw.exe")
        launcher = Path(__file__).resolve()
        arguments = f'"{launcher}"'
        work_dir = launcher.parent

    ico = ICON_FILE if ICON_FILE.exists() else ""

    ps_cmd = (
        f"$ws = New-Object -ComObject WScript.Shell; "
        f"$s = $ws.CreateShortcut('{lnk}'); "
        f"$s.TargetPath = '{target_path}'; "
        + (f"$s.Arguments = '{arguments}'; " if arguments else "")
        + f"$s.WorkingDirectory = '{work_dir}'; "
        + (f"$s.IconLocation = '{ico}'; " if ico else "")
        + f"$s.Description = 'Cinema Streaming Server for iPad, PC & Mobile'; "
        f"$s.Save()"
    )
    try:
        subprocess.run(
            ["powershell", "-NoProfile", "-Command", ps_cmd],
            check=True,
            creationflags=0x08000000 if os.name == "nt" else 0
        )
        return True, str(lnk)
    except Exception as e:
        return False, str(e)


class CinemaLauncherBackend:
    def __init__(self):
        self.cfg = load_config()
        self.proc = None
        self.is_running = False
        self.local_ip = get_local_ip()
        self.logs = []
        self.log_lock = threading.Lock()
        self.last_heartbeat = time.time()
        self.shutdown_event = threading.Event()

        # Log initial welcome messages
        self.append_log("Cinema Launcher ready.")
        self.append_log(f"Detected Local IP: {self.local_ip}")
        self.append_log("Click 'Start Cinema Server' to begin.")
        self.append_log("-" * 55)

    def append_log(self, text):
        with self.log_lock:
            # Split lines cleanly
            for line in text.splitlines():
                if line.strip():
                    self.logs.append(line)
            # Cap log buffer in memory to 2000 lines
            if len(self.logs) > 2000:
                self.logs = self.logs[-1500:]

    def get_logs_since(self, index):
        with self.log_lock:
            if index < len(self.logs):
                return self.logs[index:], len(self.logs)
            return [], len(self.logs)

    def browse_folder(self, initial=None):
        target = initial or self.cfg.get("movie_dir", r"I:\Movies")
        if not os.path.isdir(target):
            target = r"I:\Movies"

        chosen = None
        try:
            import tkinter as tk
            from tkinter import filedialog
            root = tk.Tk()
            root.withdraw()
            root.attributes("-topmost", True)
            chosen = filedialog.askdirectory(initialdir=target, title="Select Movie & Series Folder")
            root.destroy()
        except Exception:
            pass

        if chosen:
            chosen = chosen.replace("/", "\\")
            self.cfg["movie_dir"] = chosen
            save_config(self.cfg)
            return chosen
        return None

    def start_server(self, movie_dir=None, port=None, auto_start=None):
        if self.is_running:
            return True, "Server already running"

        if movie_dir:
            self.cfg["movie_dir"] = movie_dir
        if port:
            try:
                self.cfg["port"] = int(port)
            except ValueError:
                return False, "Port must be a valid number (e.g. 8000)."
        if auto_start is not None:
            self.cfg["auto_start"] = bool(auto_start)

        movie_dir_val = self.cfg.get("movie_dir", r"I:\Movies")
        port_val = self.cfg.get("port", 8000)

        if not os.path.isdir(movie_dir_val):
            return False, f"The media folder does not exist:\n{movie_dir_val}\n\nPlease check the path and try again."

        is_frozen = getattr(sys, "frozen", False)
        if not is_frozen and not SERVER_SCRIPT.exists():
            return False, f"Server script missing:\n{SERVER_SCRIPT}"

        save_config(self.cfg)
        self.local_ip = get_local_ip()

        env = os.environ.copy()
        env["MOVIE_DIR"] = movie_dir_val
        env["PORT"] = str(port_val)
        env["PYTHONUNBUFFERED"] = "1"

        if is_frozen:
            cmd = [sys.executable, "--server"]
        else:
            py_exe = sys.executable
            if "pythonw.exe" in py_exe.lower():
                alt = Path(py_exe).with_name("python.exe")
                if alt.exists():
                    py_exe = str(alt)
            cmd = [py_exe, "-u", str(SERVER_SCRIPT)]

        self.append_log(f"\n[Starting Cinema Server on port {port_val} with library: {movie_dir_val}...]")
        try:
            self.proc = subprocess.Popen(
                cmd,
                env=env,
                cwd=str(BASE_DIR),
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                encoding="utf-8",
                errors="replace",
                bufsize=1,
                creationflags=0x08000000 if os.name == "nt" else 0  # CREATE_NO_WINDOW
            )
            self.is_running = True
            threading.Thread(target=self._read_server_output, daemon=True).start()
            return True, "Started"
        except Exception as e:
            self.append_log(f"Failed to start server process: {e}")
            return False, str(e)

    def _read_server_output(self):
        try:
            for line in self.proc.stdout:
                self.append_log(line)
        except Exception:
            pass
        finally:
            self.is_running = False
            self.append_log("\n[Server stopped]")

    def stop_server(self):
        if not self.proc:
            self.is_running = False
            return True
        self.append_log("\n[Stopping Cinema Server...]")
        try:
            self.proc.terminate()
            threading.Thread(target=self._wait_and_kill, daemon=True).start()
        except Exception as e:
            self.append_log(f"Error stopping server: {e}")
        return True

    def _wait_and_kill(self):
        try:
            self.proc.wait(timeout=2.5)
        except Exception:
            try:
                self.proc.kill()
            except Exception:
                pass
        self.is_running = False

    def on_close(self):
        save_config(self.cfg)
        if self.is_running and self.proc:
            try:
                self.proc.terminate()
                self.proc.wait(timeout=1.5)
            except Exception:
                try:
                    self.proc.kill()
                except Exception:
                    pass
        self.shutdown_event.set()


def create_request_handler(backend):
    class LauncherHTTPHandler(BaseHTTPRequestHandler):
        def log_message(self, format, *args):
            # Suppress normal HTTP request logging in terminal
            return

        def _send_json(self, data, status=200):
            body = json.dumps(data).encode("utf-8")
            self.send_response(status)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Access-Control-Allow-Origin", "*")
            self.end_headers()
            self.wfile.write(body)

        def _read_body_json(self):
            try:
                length = int(self.headers.get("Content-Length", 0))
                if length > 0:
                    raw = self.rfile.read(length).decode("utf-8")
                    return json.loads(raw)
            except Exception:
                pass
            return {}

        def do_GET(self):
            parsed = urlparse(self.path)
            path = parsed.path

            if path in ("", "/", "/index.html"):
                if UI_FILE.exists():
                    try:
                        content = UI_FILE.read_bytes()
                    except Exception:
                        content = b"<h1>Launcher UI file missing</h1>"
                else:
                    content = b"<h1>Launcher UI file missing</h1>"

                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(content)))
                self.end_headers()
                self.wfile.write(content)

            elif path == "/cinema.ico" and ICON_FILE.exists():
                data = ICON_FILE.read_bytes()
                self.send_response(200)
                self.send_header("Content-Type", "image/x-icon")
                self.send_header("Content-Length", str(len(data)))
                self.send_header("Cache-Control", "no-cache")
                self.end_headers()
                self.wfile.write(data)

            elif path in ("/cinema.png", "/cinema-512.png") and PNG_ICON_512.exists():
                data = PNG_ICON_512.read_bytes()
                self.send_response(200)
                self.send_header("Content-Type", "image/png")
                self.send_header("Content-Length", str(len(data)))
                self.send_header("Cache-Control", "no-cache")
                self.end_headers()
                self.wfile.write(data)

            elif path == "/cinema-192.png" and PNG_ICON_192.exists():
                data = PNG_ICON_192.read_bytes()
                self.send_response(200)
                self.send_header("Content-Type", "image/png")
                self.send_header("Content-Length", str(len(data)))
                self.send_header("Cache-Control", "no-cache")
                self.end_headers()
                self.wfile.write(data)

            elif path == "/cinema-32.png" and PNG_ICON_32.exists():
                data = PNG_ICON_32.read_bytes()
                self.send_response(200)
                self.send_header("Content-Type", "image/png")
                self.send_header("Content-Length", str(len(data)))
                self.send_header("Cache-Control", "no-cache")
                self.end_headers()
                self.wfile.write(data)

            elif path == "/manifest.json" and MANIFEST_FILE.exists():
                data = MANIFEST_FILE.read_bytes()
                self.send_response(200)
                self.send_header("Content-Type", "application/manifest+json; charset=utf-8")
                self.send_header("Content-Length", str(len(data)))
                self.send_header("Cache-Control", "no-cache")
                self.end_headers()
                self.wfile.write(data)

            elif path == "/api/status":
                backend.last_heartbeat = time.time()
                self._send_json({
                    "is_running": backend.is_running,
                    "local_ip": backend.local_ip,
                    "movie_dir": backend.cfg.get("movie_dir", r"I:\Movies"),
                    "port": backend.cfg.get("port", 8000),
                    "auto_start": backend.cfg.get("auto_start", False),
                })

            elif path == "/api/logs":
                backend.last_heartbeat = time.time()
                qs = parse_qs(parsed.query)
                since = int(qs.get("since", [0])[0])
                lines, next_cursor = backend.get_logs_since(since)
                self._send_json({
                    "lines": lines,
                    "next": next_cursor,
                    "is_running": backend.is_running
                })

            else:
                self.send_response(404)
                self.end_headers()

        def do_POST(self):
            parsed = urlparse(self.path)
            path = parsed.path
            backend.last_heartbeat = time.time()

            if path == "/api/browse":
                body = self._read_body_json()
                chosen = backend.browse_folder(body.get("current"))
                self._send_json({"movie_dir": chosen})

            elif path == "/api/config":
                body = self._read_body_json()
                if "movie_dir" in body:
                    backend.cfg["movie_dir"] = body["movie_dir"]
                if "port" in body:
                    try:
                        backend.cfg["port"] = int(body["port"])
                    except ValueError:
                        pass
                if "auto_start" in body:
                    backend.cfg["auto_start"] = bool(body["auto_start"])
                save_config(backend.cfg)
                self._send_json({"ok": True})

            elif path == "/api/start":
                body = self._read_body_json()
                ok, msg = backend.start_server(
                    movie_dir=body.get("movie_dir"),
                    port=body.get("port"),
                    auto_start=body.get("auto_start")
                )
                self._send_json({"ok": ok, "error": msg if not ok else None})

            elif path == "/api/stop":
                backend.stop_server()
                self._send_json({"ok": True})

            elif path == "/api/shortcut":
                ok, res = make_desktop_shortcut()
                self._send_json({"ok": ok, "message": res})

            elif path == "/api/open_pc":
                body = self._read_body_json()
                url = body.get("url") or f"http://localhost:{backend.cfg.get('port', 8000)}"
                webbrowser.open(url)
                self._send_json({"ok": True})

            elif path == "/api/heartbeat":
                backend.last_heartbeat = time.time()
                self._send_json({"ok": True})

            elif path == "/api/exit":
                backend.shutdown_event.set()
                self._send_json({"ok": True})

            else:
                self.send_response(404)
                self.end_headers()

    return LauncherHTTPHandler


def find_edge_browser():
    candidates = [
        r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe",
        r"C:\Program Files\Microsoft\Edge\Application\msedge.exe",
    ]
    for p in candidates:
        if os.path.isfile(p):
            return p
    return None


def start_launcher_http_server(backend):
    ports_to_try = [8765, 8766, 8767, 0]
    for p in ports_to_try:
        try:
            server = ThreadingHTTPServer(("127.0.0.1", p), create_request_handler(backend))
            actual_port = server.server_port
            server_thread = threading.Thread(target=server.serve_forever, daemon=True)
            server_thread.start()

            # Verify socket readiness so the browser never connects prematurely
            deadline = time.time() + 2.5
            ready = False
            while time.time() < deadline:
                try:
                    with socket.create_connection(("127.0.0.1", actual_port), timeout=0.2):
                        ready = True
                        break
                except OSError:
                    time.sleep(0.05)

            if ready:
                return server, actual_port
            else:
                server.shutdown()
        except OSError:
            continue
    raise RuntimeError("Failed to bind Cinema launcher HTTP server to any port.")


def main():
    backend = CinemaLauncherBackend()

    # Bind HTTP server with connection readiness guarantee
    server, port = start_launcher_http_server(backend)
    url = f"http://127.0.0.1:{port}"

    # Auto-start server if configured
    if backend.cfg.get("auto_start"):
        threading.Timer(0.6, lambda: backend.start_server()).start()

    edge_exe = find_edge_browser()
    try:
        import ctypes
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("Cinema.Server.Launcher.1.0")
    except Exception:
        pass

    edge_proc = None

    if edge_exe:
        # Launch dedicated Edge app window
        profile_dir = Path(os.environ.get("LOCALAPPDATA", str(BASE_DIR))) / "CinemaServerLauncher" / "edge_profile"
        profile_dir.mkdir(parents=True, exist_ok=True)

        # Remove stale lock files that might cause Edge to delegate or fail
        for lock_name in ["SingletonLock", "SingletonCookie", "SingletonSocket"]:
            lock_path = profile_dir / lock_name
            if lock_path.exists():
                try:
                    lock_path.unlink()
                except Exception:
                    pass

        # Remove stale cached favicon in profile so Edge refreshes newly generated icons
        for f_name in ["Favicons", "Favicons-journal"]:
            f_path = profile_dir / "Default" / f_name
            if f_path.exists():
                try:
                    f_path.unlink()
                except Exception:
                    pass

        cmd = [
            edge_exe,
            f"--app={url}",
            f"--user-data-dir={profile_dir}",
            "--app-id=CinemaServerLauncher",
            "--window-size=1120,860",
            "--no-first-run",
            "--no-default-browser-check",
            "--disable-background-mode",
        ]
        try:
            edge_proc = subprocess.Popen(cmd)
            # Apply native taskbar and titlebar window icon via Win32 API
            threading.Thread(target=apply_native_window_icon, args=(ICON_FILE, "Cinema Server Launcher"), daemon=True).start()
        except Exception:
            webbrowser.open(url)
    else:
        webbrowser.open(url)

    # Monitor browser lifetime or heartbeat
    window_title = "Cinema Server Launcher"
    startup_time = time.time()
    window_seen = False
    window_missing_count = 0

    try:
        while not backend.shutdown_event.is_set():
            time.sleep(0.5)

            # Check if native window exists
            hwnd = 0
            if os.name == "nt":
                try:
                    import ctypes
                    hwnd = ctypes.windll.user32.FindWindowW(None, window_title)
                except Exception:
                    hwnd = 0

            if hwnd:
                window_seen = True
                window_missing_count = 0
            elif window_seen:
                window_missing_count += 1
                # Window was previously open, but has now been missing for 3 consecutive seconds (6 * 0.5s)
                if window_missing_count >= 6:
                    break

            # If window has been seen and is still present (hwnd != 0), do not kill on heartbeat timeout!
            # Heartbeats might be throttled by Chromium when minimized.
            if hwnd != 0:
                continue

            # If edge_proc exited after startup grace period and window was never seen
            elapsed = time.time() - startup_time
            if elapsed > 15 and not window_seen:
                if edge_proc and edge_proc.poll() is not None:
                    break
                if time.time() - backend.last_heartbeat > 30:
                    break

            # Generous safety fallback if window was not found or closed without beforeunload
            if time.time() - backend.last_heartbeat > 120:
                break
    except KeyboardInterrupt:
        pass
    finally:
        backend.on_close()
        server.shutdown()


if __name__ == "__main__":
    if "--server" in sys.argv:
        import portfilespacificforipad
        portfilespacificforipad.main()
    else:
        main()
