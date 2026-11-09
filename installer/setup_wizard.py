"""
Cinema Server Setup Wizard
A self-contained Windows installer wizard for Cinema Server.
"""

import os
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

BASE_DIR = Path(sys.executable).parent.resolve() if getattr(sys, "frozen", False) else Path(__file__).parent.resolve()
ROOT_DIR = BASE_DIR if (BASE_DIR / "portfilespacificforipad.py").exists() else BASE_DIR.parent
BUNDLE_DIR = Path(getattr(sys, "_MEIPASS", ROOT_DIR))


def resolve_file(filename, subfolder=""):
    candidates = []
    if subfolder:
        candidates.append(BUNDLE_DIR / subfolder / filename)
        candidates.append(ROOT_DIR / subfolder / filename)
    candidates.append(BUNDLE_DIR / filename)
    candidates.append(ROOT_DIR / filename)
    for c in candidates:
        if c.exists():
            return c
    return ROOT_DIR / (Path(subfolder) / filename if subfolder else filename)


ICON_FILE = resolve_file("cinema.ico", "assets")
PAYLOAD_EXE = resolve_file("Cinema.exe")


def get_default_install_dir():
    local_app_data = os.environ.get("LOCALAPPDATA")
    if local_app_data:
        return os.path.join(local_app_data, "Cinema")
    user_prof = os.environ.get("USERPROFILE", "")
    return os.path.join(user_prof, "Cinema") if user_prof else r"C:\Cinema"


def create_shortcut(target_exe, lnk_path, icon_path=None, description="Cinema Streaming Server for iPad & PC"):
    target_exe = Path(target_exe).resolve()
    lnk_path = Path(lnk_path).resolve()
    lnk_path.parent.mkdir(parents=True, exist_ok=True)
    work_dir = target_exe.parent
    ico = str(Path(icon_path).resolve()) if icon_path and Path(icon_path).exists() else str(target_exe)

    ps_cmd = (
        f"$ws = New-Object -ComObject WScript.Shell; "
        f"$s = $ws.CreateShortcut('{lnk_path}'); "
        f"$s.TargetPath = '{target_exe}'; "
        f"$s.WorkingDirectory = '{work_dir}'; "
        f"$s.IconLocation = '{ico}'; "
        f"$s.Description = '{description}'; "
        f"$s.Save()"
    )
    try:
        subprocess.run(
            ["powershell", "-NoProfile", "-Command", ps_cmd],
            check=True,
            creationflags=0x08000000 if os.name == "nt" else 0
        )
        return True
    except Exception:
        return False


class CinemaSetupWizard:
    def __init__(self, root):
        self.root = root
        self.root.title("Cinema Server Setup")
        self.root.geometry("540x440")
        self.root.resizable(False, False)
        self.root.configure(bg="#0a0b10")

        # Center on screen
        self.root.update_idletasks()
        w = 540
        h = 440
        x = (self.root.winfo_screenwidth() // 2) - (w // 2)
        y = (self.root.winfo_screenheight() // 2) - (h // 2)
        self.root.geometry(f"{w}x{h}+{x}+{y}")

        if ICON_FILE.exists():
            try:
                self.root.iconbitmap(str(ICON_FILE))
            except Exception:
                pass

        # Colors
        self.c_bg = "#0a0b10"
        self.c_card = "#12131c"
        self.c_border = "#222330"
        self.c_text = "#f2f4fa"
        self.c_muted = "#98a2b8"
        self.c_accent = "#ff7a1a"
        self.c_green = "#34e5a0"

        # State Variables
        self.dest_var = tk.StringVar(value=get_default_install_dir())
        self.chk_desktop_var = tk.BooleanVar(value=True)
        self.chk_startmenu_var = tk.BooleanVar(value=True)
        self.chk_launch_var = tk.BooleanVar(value=True)

        self._build_welcome_screen()

    def _build_welcome_screen(self):
        for w in self.root.winfo_children():
            w.destroy()

        main = tk.Frame(self.root, bg=self.c_bg, padx=28, pady=24)
        main.pack(fill=tk.BOTH, expand=True)

        # Header with Logo Tile & Title
        header = tk.Frame(main, bg=self.c_bg)
        header.pack(fill=tk.X, pady=(0, 18))

        # Title text
        title_lbl = tk.Label(
            header,
            text="CINEMA SERVER SETUP",
            font=("Segoe UI", 16, "bold"),
            fg=self.c_accent,
            bg=self.c_bg,
            anchor="w"
        )
        title_lbl.pack(anchor="w")

        subtitle_lbl = tk.Label(
            header,
            text="Install Cinema Server to stream movies & anime to iPad, iPhone & PC.",
            font=("Segoe UI", 10),
            fg=self.c_muted,
            bg=self.c_bg,
            anchor="w"
        )
        subtitle_lbl.pack(anchor="w", pady=(2, 0))

        # Destination Card
        card_dest = tk.Frame(main, bg=self.c_card, highlightbackground=self.c_border, highlightthickness=1, padx=16, pady=14)
        card_dest.pack(fill=tk.X, pady=(0, 14))

        tk.Label(
            card_dest,
            text="DESTINATION FOLDER",
            font=("Segoe UI", 9, "bold"),
            fg=self.c_muted,
            bg=self.c_card
        ).pack(anchor="w", pady=(0, 6))

        row_dest = tk.Frame(card_dest, bg=self.c_card)
        row_dest.pack(fill=tk.X)

        entry_dest = tk.Entry(
            row_dest,
            textvariable=self.dest_var,
            font=("Segoe UI", 10),
            bg="#08080d",
            fg=self.c_text,
            insertbackground=self.c_accent,
            relief=tk.FLAT,
            bd=5
        )
        entry_dest.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 8))

        btn_browse = tk.Button(
            row_dest,
            text="Browse...",
            font=("Segoe UI", 9, "bold"),
            bg="#222332",
            fg="#ffffff",
            activebackground="#2e2f42",
            activeforeground="#ffffff",
            relief=tk.FLAT,
            padx=12,
            pady=3,
            cursor="hand2",
            command=self._browse_dest
        )
        btn_browse.pack(side=tk.RIGHT)

        # Options Card
        card_opts = tk.Frame(main, bg=self.c_card, highlightbackground=self.c_border, highlightthickness=1, padx=16, pady=12)
        card_opts.pack(fill=tk.X, pady=(0, 20))

        tk.Label(
            card_opts,
            text="INSTALLATION SHORTCUTS",
            font=("Segoe UI", 9, "bold"),
            fg=self.c_muted,
            bg=self.c_card
        ).pack(anchor="w", pady=(0, 8))

        chk1 = tk.Checkbutton(
            card_opts,
            text="Create Desktop Shortcut",
            variable=self.chk_desktop_var,
            font=("Segoe UI", 10),
            bg=self.c_card,
            fg=self.c_text,
            activebackground=self.c_card,
            activeforeground="#ffffff",
            selectcolor="#08080d"
        )
        chk1.pack(anchor="w", pady=2)

        chk2 = tk.Checkbutton(
            card_opts,
            text="Add to Windows Start Menu",
            variable=self.chk_startmenu_var,
            font=("Segoe UI", 10),
            bg=self.c_card,
            fg=self.c_text,
            activebackground=self.c_card,
            activeforeground="#ffffff",
            selectcolor="#08080d"
        )
        chk2.pack(anchor="w", pady=2)

        chk3 = tk.Checkbutton(
            card_opts,
            text="Launch Cinema Server after installation",
            variable=self.chk_launch_var,
            font=("Segoe UI", 10),
            bg=self.c_card,
            fg=self.c_text,
            activebackground=self.c_card,
            activeforeground="#ffffff",
            selectcolor="#08080d"
        )
        chk3.pack(anchor="w", pady=2)

        # Bottom Action Buttons
        btn_bar = tk.Frame(main, bg=self.c_bg)
        btn_bar.pack(fill=tk.X, side=tk.BOTTOM)

        btn_cancel = tk.Button(
            btn_bar,
            text="Cancel",
            font=("Segoe UI", 10),
            bg="#181822",
            fg=self.c_muted,
            activebackground="#222332",
            activeforeground="#ffffff",
            relief=tk.FLAT,
            padx=18,
            pady=6,
            cursor="hand2",
            command=self.root.destroy
        )
        btn_cancel.pack(side=tk.LEFT)

        btn_install = tk.Button(
            btn_bar,
            text="▶   INSTALL CINEMA SERVER",
            font=("Segoe UI", 10, "bold"),
            bg=self.c_accent,
            fg="#14090a",
            activebackground="#ff8c3a",
            activeforeground="#14090a",
            relief=tk.FLAT,
            padx=22,
            pady=6,
            cursor="hand2",
            command=self._start_install
        )
        btn_install.pack(side=tk.RIGHT)

    def _browse_dest(self):
        chosen = filedialog.askdirectory(initialdir=self.dest_var.get(), title="Select Installation Folder")
        if chosen:
            self.dest_var.set(os.path.join(chosen.replace("/", "\\"), "Cinema"))

    def _start_install(self):
        target = self.dest_var.get().strip()
        if not target:
            messagebox.showerror("Error", "Please select a destination folder.")
            return

        # Build progress screen
        for w in self.root.winfo_children():
            w.destroy()

        main = tk.Frame(self.root, bg=self.c_bg, padx=32, pady=32)
        main.pack(fill=tk.BOTH, expand=True)

        tk.Label(
            main,
            text="INSTALLING CINEMA SERVER",
            font=("Segoe UI", 15, "bold"),
            fg=self.c_accent,
            bg=self.c_bg
        ).pack(anchor="w", pady=(0, 6))

        self.status_lbl = tk.Label(
            main,
            text="Extracting application files...",
            font=("Segoe UI", 10),
            fg=self.c_muted,
            bg=self.c_bg
        )
        self.status_lbl.pack(anchor="w", pady=(0, 16))

        # Progress bar
        style = ttk.Style()
        style.theme_use("clam")
        style.configure(
            "Orange.Horizontal.TProgressbar",
            troughcolor="#12131c",
            background="#ff7a1a",
            lightcolor="#ff7a1a",
            darkcolor="#ff7a1a",
            bordercolor="#222330",
            thickness=14
        )

        self.prog = ttk.Progressbar(main, style="Orange.Horizontal.TProgressbar", mode="determinate", length=470)
        self.prog.pack(fill=tk.X, pady=(0, 20))
        self.prog["value"] = 10

        self.detail_lbl = tk.Label(
            main,
            text="Preparing destination directory...",
            font=("Consolas", 9),
            fg="#64748b",
            bg=self.c_bg,
            anchor="w"
        )
        self.detail_lbl.pack(anchor="w")

        threading.Thread(target=self._run_install_thread, daemon=True).start()

    def _run_install_thread(self):
        target_dir = Path(self.dest_var.get().strip())
        target_dir.mkdir(parents=True, exist_ok=True)

        time.sleep(0.3)
        self._update_progress(25, "Extracting Cinema application bundle...", f"Target: {target_dir}")

        dest_exe = target_dir / "Cinema.exe"
        dest_ico = target_dir / "cinema.ico"

        try:
            # 1. Copy or extract Cinema.exe payload
            if PAYLOAD_EXE.exists():
                shutil.copy2(str(PAYLOAD_EXE), str(dest_exe))
            else:
                # If running directly from workspace, package files
                raise FileNotFoundError(f"Payload not found at {PAYLOAD_EXE}")

            self._update_progress(60, "Configuring FFmpeg and media engine...", f"Installed {dest_exe.name}")
            time.sleep(0.3)

            # 2. Copy icons and manifest
            dest_assets = target_dir / "assets"
            dest_assets.mkdir(parents=True, exist_ok=True)
            for extra in ["cinema.ico", "cinema.png", "cinema-192.png", "cinema-32.png", "manifest.json"]:
                src = resolve_file(extra, "assets")
                if src.exists():
                    try:
                        shutil.copy2(str(src), str(dest_assets / extra))
                        if extra == "cinema.ico":
                            shutil.copy2(str(src), str(dest_ico))
                    except Exception:
                        pass

            self._update_progress(80, "Creating shortcuts...", "Configuring Windows Desktop and Start Menu shortcuts...")
            time.sleep(0.2)

            # 3. Create Desktop shortcut
            if self.chk_desktop_var.get():
                desktop = Path(os.environ.get("USERPROFILE", "")) / "Desktop"
                if desktop.exists():
                    lnk = desktop / "Cinema Server.lnk"
                    create_shortcut(dest_exe, lnk, dest_ico)

            # 4. Create Start Menu shortcut
            if self.chk_startmenu_var.get():
                appdata = os.environ.get("APPDATA", "")
                if appdata:
                    start_programs = Path(appdata) / "Microsoft" / "Windows" / "Start Menu" / "Programs"
                    if start_programs.exists():
                        lnk = start_programs / "Cinema Server.lnk"
                        create_shortcut(dest_exe, lnk, dest_ico)

            self._update_progress(100, "Setup complete!", "Cinema Server successfully installed.")
            time.sleep(0.4)

            self.root.after(0, lambda: self._show_complete_screen(dest_exe))

        except Exception as e:
            self.root.after(0, lambda: messagebox.showerror("Installation Error", f"Failed to install Cinema Server:\n{e}"))
            self.root.after(0, self._build_welcome_screen)

    def _update_progress(self, val, status_text, detail_text=""):
        def _apply():
            self.prog["value"] = val
            self.status_lbl.configure(text=status_text)
            self.detail_lbl.configure(text=detail_text)
        self.root.after(0, _apply)

    def _show_complete_screen(self, installed_exe):
        for w in self.root.winfo_children():
            w.destroy()

        main = tk.Frame(self.root, bg=self.c_bg, padx=32, pady=32)
        main.pack(fill=tk.BOTH, expand=True)

        # Success badge
        tk.Label(
            main,
            text="✔   INSTALLATION COMPLETE",
            font=("Segoe UI", 16, "bold"),
            fg=self.c_green,
            bg=self.c_bg
        ).pack(anchor="w", pady=(0, 8))

        tk.Label(
            main,
            text="Cinema Server has been successfully installed on your computer!",
            font=("Segoe UI", 11),
            fg=self.c_text,
            bg=self.c_bg
        ).pack(anchor="w", pady=(0, 4))

        tk.Label(
            main,
            text=f"Installed to:\n{installed_exe.parent}",
            font=("Consolas", 9),
            fg=self.c_muted,
            bg=self.c_bg,
            justify=tk.LEFT
        ).pack(anchor="w", pady=(0, 16))

        card_info = tk.Frame(main, bg=self.c_card, highlightbackground=self.c_border, highlightthickness=1, padx=16, pady=12)
        card_info.pack(fill=tk.X, pady=(0, 24))

        tk.Label(
            card_info,
            text="✨ You can now start Cinema Server anytime from your Desktop shortcut.",
            font=("Segoe UI", 10),
            fg=self.c_text,
            bg=self.c_card
        ).pack(anchor="w")

        btn_bar = tk.Frame(main, bg=self.c_bg)
        btn_bar.pack(fill=tk.X, side=tk.BOTTOM)

        def _finish():
            if self.chk_launch_var.get() and installed_exe.exists():
                try:
                    subprocess.Popen(
                        [str(installed_exe)],
                        cwd=str(installed_exe.parent),
                        creationflags=0x08000000 if os.name == "nt" else 0
                    )
                except Exception:
                    pass
            self.root.destroy()

        btn_finish = tk.Button(
            btn_bar,
            text="Finish & Launch Cinema Server" if self.chk_launch_var.get() else "Finish",
            font=("Segoe UI", 11, "bold"),
            bg=self.c_green,
            fg="#07080d",
            activebackground="#45f5b0",
            activeforeground="#07080d",
            relief=tk.FLAT,
            padx=24,
            pady=8,
            cursor="hand2",
            command=_finish
        )
        btn_finish.pack(side=tk.RIGHT)


def main():
    root = tk.Tk()
    app = CinemaSetupWizard(root)
    root.mainloop()


if __name__ == "__main__":
    main()

