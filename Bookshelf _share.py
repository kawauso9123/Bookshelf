import os
import sys
import time
import sqlite3
import pathlib
import subprocess
import hashlib
import zipfile
import re
import io
import threading
import ctypes
import uuid
from collections import deque
from dataclasses import dataclass
from typing import Optional, List, Dict, Set, Tuple

from PyQt6.QtCore import (
    Qt, QAbstractListModel, QModelIndex, QSize,
    QObject, pyqtSignal, QRunnable, QThreadPool, QTimer, QSettings, QRect, QPoint, QEvent
)
from PyQt6.QtGui import QIcon, QPixmap, QAction, QPainter, QFont, QShortcut, QKeySequence, QWheelEvent, QMouseEvent
from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QListView, QPushButton, QLabel, QLineEdit, QComboBox, QMessageBox,
    QFileDialog, QMenu, QAbstractItemView
)

from PIL import Image
import fitz  # PyMuPDF

# =========================
# USER SETTINGS
# =========================
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE_DIR, "data")

VIEWER_EXE = r""
# =========================

APP_NAME = "ZipPlaLikeShelf"
DB_NAME = "library.sqlite3"

THUMB_SIZE = 320         # サムネ長辺
THUMB_VER = 3            # サムネ方式のバージョン
MAX_THUMB_JOBS = 12      # 同時生成数（NAS負荷を抑える）

IMG_EXTS = {".jpg", ".jpeg", ".png", ".webp", ".gif", ".bmp"}

# 混在ビュー（子フォルダカード＋直下の本）用：フォルダカード先頭表示
SHOW_DIRS_FIRST = True


def norm(path: str) -> str:
    return os.path.normpath(path)

def ensure_dir(p: str) -> None:
    os.makedirs(p, exist_ok=True)

def natural_key(s: str):
    return [int(t) if t.isdigit() else t.lower() for t in re.split(r"(\d+)", s)]

def sha1(s: str) -> str:
    return hashlib.sha1(s.encode("utf-8", "ignore")).hexdigest()

def is_image_name(name: str) -> bool:
    ext = os.path.splitext(name.lower())[1]
    return ext in IMG_EXTS


# -----------------------------
# DB
# -----------------------------
class LibraryDB:
    def __init__(self, db_path: str):
        self.db_path = db_path
        self._lock = threading.RLock()
        self.conn = sqlite3.connect(self.db_path, check_same_thread=False)
        self.conn.row_factory = sqlite3.Row
        self._init()

    def _init(self) -> None:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("PRAGMA journal_mode=WAL;")
            cur.execute("PRAGMA synchronous=NORMAL;")
            cur.execute("""
            CREATE TABLE IF NOT EXISTS roots(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                path TEXT UNIQUE NOT NULL,
                created_at INTEGER NOT NULL
            );
            """)
            cur.execute("""
            CREATE TABLE IF NOT EXISTS books(
                path TEXT PRIMARY KEY,
                root_id INTEGER NOT NULL,
                rel_path TEXT NOT NULL,
                parent_dir TEXT NOT NULL,
                type TEXT NOT NULL,            -- 'zip','pdf','img'
                size INTEGER NOT NULL,
                mtime INTEGER NOT NULL,
                title TEXT NOT NULL,
                cover_state INTEGER NOT NULL DEFAULT 0,  -- 0=none,1=ok,2=fail
                cover_thumb_path TEXT,
                cover_sig TEXT,
                last_scanned_at INTEGER NOT NULL,
                FOREIGN KEY(root_id) REFERENCES roots(id)
            );
            """)
            cur.execute("""
            CREATE TABLE IF NOT EXISTS meta(
                path TEXT PRIMARY KEY,
                rating INTEGER NOT NULL DEFAULT 0
            );
            """)

            # ディレクトリ一覧（books逆算ではなく、実ディレクトリを保持）
            cur.execute("""
            CREATE TABLE IF NOT EXISTS dirs(
                root_id INTEGER NOT NULL,
                rel_dir TEXT NOT NULL,      -- "" がルート
                parent_dir TEXT NOT NULL,   -- "" がルート
                name TEXT NOT NULL,         -- 表示名（末尾要素。ルートは ""）
                mtime INTEGER NOT NULL,
                last_scanned_at INTEGER NOT NULL,
                PRIMARY KEY(root_id, rel_dir)
            );
            """)
            cur.execute("CREATE INDEX IF NOT EXISTS idx_dirs_parent ON dirs(root_id, parent_dir);")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_dirs_name ON dirs(root_id, name);")

            # booksの補助インデックス（代表選択高速化）
            cur.execute("CREATE INDEX IF NOT EXISTS idx_books_rel_path ON books(root_id, rel_path);")

            cur.execute("CREATE INDEX IF NOT EXISTS idx_books_root ON books(root_id);")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_books_parent_dir ON books(parent_dir);")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_books_title ON books(title);")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_meta_rating ON meta(rating);")
            self.conn.commit()

    def upsert_root(self, root_path: str) -> int:
        with self._lock:
            root_path = norm(root_path)
            now = int(time.time())
            cur = self.conn.cursor()
            cur.execute("""
            INSERT INTO roots(path, created_at) VALUES(?, ?)
            ON CONFLICT(path) DO UPDATE SET created_at=excluded.created_at
            """, (root_path, now))
            self.conn.commit()
            cur.execute("SELECT id FROM roots WHERE path=?", (root_path,))
            row = cur.fetchone()
            root_id = int(row["id"])

            # dirsのルート行を確保
            cur.execute("""
            INSERT OR IGNORE INTO dirs(root_id, rel_dir, parent_dir, name, mtime, last_scanned_at)
            VALUES(?, ?, ?, ?, ?, ?)
            """, (root_id, "", "", "", now, now))
            self.conn.commit()
            return root_id

    def get_roots(self) -> List[str]:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("SELECT path FROM roots ORDER BY created_at DESC")
            return [r["path"] for r in cur.fetchall()]

    def upsert_book(self, *, path: str, root_id: int, rel_path: str, parent_dir: str,
                    btype: str, size: int, mtime: int, title: str) -> None:
        with self._lock:
            now = int(time.time())
            cur = self.conn.cursor()
            cur.execute("""
            INSERT INTO books(path, root_id, rel_path, parent_dir, type, size, mtime, title, last_scanned_at)
            VALUES(?,?,?,?,?,?,?,?,?)
            ON CONFLICT(path) DO UPDATE SET
                root_id=excluded.root_id,
                rel_path=excluded.rel_path,
                parent_dir=excluded.parent_dir,
                type=excluded.type,
                size=excluded.size,
                mtime=excluded.mtime,
                title=excluded.title,
                last_scanned_at=excluded.last_scanned_at
            """, (path, root_id, rel_path, parent_dir, btype, size, mtime, title, now))
            self.conn.commit()

    def set_rating(self, path: str, rating: int) -> None:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("""
            INSERT INTO meta(path, rating) VALUES(?,?)
            ON CONFLICT(path) DO UPDATE SET rating=excluded.rating
            """, (path, int(rating)))
            self.conn.commit()

    def get_rating(self, path: str) -> int:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("SELECT rating FROM meta WHERE path=?", (path,))
            row = cur.fetchone()
            return int(row["rating"]) if row else 0

    def dir_has_star_books(self, root_id: int, rel_dir: str) -> bool:
        # rel_path は "dir\\file.zip" 形式を想定
        prefix = rel_dir.rstrip("\\/") + "\\"
        with self._lock:
            cur = self.conn.cursor()
            cur.execute(
                """
                SELECT 1
                FROM books b
                LEFT JOIN meta m ON m.path = b.path
                WHERE b.root_id = ?
                  AND b.rel_path LIKE ?
                  AND COALESCE(m.rating, 0) > 0
                LIMIT 1
                """,
                (root_id, prefix + "%"),
            )
            return cur.fetchone() is not None

    def upsert_dir(self, *, root_id: int, rel_dir: str, parent_dir: str, name: str, mtime: int) -> None:
        with self._lock:
            now = int(time.time())
            cur = self.conn.cursor()
            cur.execute("""
            INSERT INTO dirs(root_id, rel_dir, parent_dir, name, mtime, last_scanned_at)
            VALUES(?,?,?,?,?,?)
            ON CONFLICT(root_id, rel_dir) DO UPDATE SET
                parent_dir=excluded.parent_dir,
                name=excluded.name,
                mtime=excluded.mtime,
                last_scanned_at=excluded.last_scanned_at
            """, (root_id, rel_dir, parent_dir, name, int(mtime), now))
            self.conn.commit()

    def list_child_dirs(self, root_id: int, parent_dir: str, query: str = "") -> List[sqlite3.Row]:
        with self._lock:
            q = f"%{query.strip()}%" if query.strip() else "%"
            cur = self.conn.cursor()
            cur.execute("""
            SELECT rel_dir, name, mtime
            FROM dirs
            WHERE root_id=? AND parent_dir=? AND name LIKE ?
            ORDER BY name
            """, (root_id, parent_dir, q))
            return cur.fetchall()

    def list_direct_books(self, root_id: int, dir_rel: str, query: str = "", only_star: bool = False) -> List[sqlite3.Row]:
        """dir_rel直下の本だけ（混在ビュー用）"""
        with self._lock:
            q = f"%{query.strip()}%" if query.strip() else "%"
            cur = self.conn.cursor()
            if only_star:
                cur.execute("""
                SELECT b.*, COALESCE(m.rating,0) AS rating
                FROM books b
                LEFT JOIN meta m ON m.path=b.path
                WHERE b.root_id=? AND b.parent_dir=? AND COALESCE(m.rating,0) > 0
                  AND (b.title LIKE ? OR b.rel_path LIKE ?)
                ORDER BY b.title
                """, (root_id, dir_rel, q, q))
            else:
                cur.execute("""
                SELECT b.*, COALESCE(m.rating,0) AS rating
                FROM books b
                LEFT JOIN meta m ON m.path=b.path
                WHERE b.root_id=? AND b.parent_dir=?
                  AND (b.title LIKE ? OR b.rel_path LIKE ?)
                ORDER BY b.title
                """, (root_id, dir_rel, q, q))
            return cur.fetchall()

    def get_dir_rep_path(self, root_id: int, dir_rel: str, only_star: bool = False) -> Optional[Tuple[str, int]]:
        """フォルダカードの代表表紙：☆優先→mtime新しい（配下全部から1つ）"""
        with self._lock:
            cur = self.conn.cursor()
            like = (dir_rel + r"\%") if dir_rel else "%"
            if only_star:
                cur.execute("""
                SELECT b.path, COALESCE(m.rating,0) as rating
                FROM books b
                LEFT JOIN meta m ON m.path=b.path
                WHERE b.root_id=? AND b.rel_path LIKE ? AND COALESCE(m.rating,0) > 0
                ORDER BY COALESCE(m.rating,0) DESC, b.mtime DESC
                LIMIT 1
                """, (root_id, like))
            else:
                cur.execute("""
                SELECT b.path, COALESCE(m.rating,0) as rating
                FROM books b
                LEFT JOIN meta m ON m.path=b.path
                WHERE b.root_id=? AND b.rel_path LIKE ?
                ORDER BY COALESCE(m.rating,0) DESC, b.mtime DESC
                LIMIT 1
                """, (root_id, like))
            row = cur.fetchone()
            return (row["path"], int(row["rating"])) if row else None

    def list_books(self, root_id: int, query: str = "", only_star: bool = False, dir_rel: str = "") -> List[sqlite3.Row]:
        with self._lock:
            q = f"%{query.strip()}%" if query.strip() else "%"
            cur = self.conn.cursor()

            where_dir = ""
            params: list = [root_id]

            if dir_rel:
                # dir_rel配下のみ（rel_pathは \ 区切り想定）
                where_dir = " AND b.rel_path LIKE ? "
                params.append(dir_rel + r"\%")

            if only_star:
                sql = f"""
                SELECT b.*, COALESCE(m.rating,0) AS rating
                FROM books b
                LEFT JOIN meta m ON m.path=b.path
                WHERE b.root_id=? {where_dir}
                  AND COALESCE(m.rating,0) > 0
                  AND (b.title LIKE ? OR b.rel_path LIKE ?)
                ORDER BY b.parent_dir, b.title
                """
                params += [q, q]
            else:
                sql = f"""
                SELECT b.*, COALESCE(m.rating,0) AS rating
                FROM books b
                LEFT JOIN meta m ON m.path=b.path
                WHERE b.root_id=? {where_dir}
                  AND (b.title LIKE ? OR b.rel_path LIKE ?)
                ORDER BY b.parent_dir, b.title
                """
                params += [q, q]

            cur.execute(sql, tuple(params))
            return cur.fetchall()

    def list_books_recursive(self, root_id: int, dir_rel: str, query: str = "", only_star: bool = False) -> List[sqlite3.Row]:
        with self._lock:
            q = f"%{query.strip()}%" if query.strip() else "%"
            like = (dir_rel + r"\%") if dir_rel else "%"
            cur = self.conn.cursor()

            if only_star:
                cur.execute("""
                SELECT b.*, COALESCE(m.rating,0) AS rating
                FROM books b
                LEFT JOIN meta m ON m.path=b.path
                WHERE b.root_id=? AND b.rel_path LIKE ? AND COALESCE(m.rating,0) > 0
                  AND (b.title LIKE ? OR b.rel_path LIKE ?)
                ORDER BY b.parent_dir, b.title
                """, (root_id, like, q, q))
            else:
                cur.execute("""
                SELECT b.*, COALESCE(m.rating,0) AS rating
                FROM books b
                LEFT JOIN meta m ON m.path=b.path
                WHERE b.root_id=? AND b.rel_path LIKE ?
                  AND (b.title LIKE ? OR b.rel_path LIKE ?)
                ORDER BY b.parent_dir, b.title
                """, (root_id, like, q, q))
            return cur.fetchall()

    def list_folder_buckets(self, root_id: int, query: str = "", only_star: bool = False, dir_rel: str = "") -> List[dict]:
        with self._lock:
            rows = self.list_books(root_id, query=query, only_star=only_star, dir_rel=dir_rel)
            buckets: Dict[str, tuple] = {}
            
            base = dir_rel.replace("\\", "/").strip("/")
            prefix = base + "/" if base else ""

            for r in rows:
                rel = r["rel_path"].replace("\\", "/")
                
                if prefix:
                    if not rel.startswith(prefix):
                        continue
                    rel2 = rel[len(prefix):]
                else:
                    rel2 = rel

                parts = rel2.split("/")
                child = parts[0] if len(parts) > 1 else "."
                cand = (int(r["rating"]), int(r["mtime"]), r["title"], r["path"])
                prev = buckets.get(child)
                if prev is None or cand > prev:
                    buckets[child] = cand

            out = []
            for child, (rating, mtime, title, path) in sorted(buckets.items(), key=lambda x: x[0]):
                out.append({"child": child, "rep_path": path, "rating": rating})
            return out

    def get_thumb_info(self, path: str) -> Optional[sqlite3.Row]:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("SELECT cover_thumb_path, cover_sig, cover_state, mtime, size, type FROM books WHERE path=?", (path,))
            return cur.fetchone()

    def set_thumb_ok(self, path: str, thumb_path: str, cover_sig: str) -> None:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("""
            UPDATE books SET cover_state=1, cover_thumb_path=?, cover_sig=?
            WHERE path=?
            """, (thumb_path, cover_sig, path))
            self.conn.commit()

    def set_thumb_fail(self, path: str, cover_sig: str) -> None:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("""
            UPDATE books SET cover_state=2, cover_sig=?
            WHERE path=?
            """, (cover_sig, path))
            self.conn.commit()


# -----------------------------
# Scan worker (Phase A)
# -----------------------------
class ScanSignals(QObject):
    progress = pyqtSignal(str)
    finished = pyqtSignal(int)
    error = pyqtSignal(str)

class ScanJob(QRunnable):
    def __init__(self, db: LibraryDB, root_id: int, root_path: str):
        super().__init__()
        self.db = db
        self.root_id = root_id
        self.root_path = norm(root_path)
        self.signals = ScanSignals()

    @staticmethod
    def _classify(path: str) -> Optional[str]:
        ext = os.path.splitext(path.lower())[1]
        if ext == ".zip":
            return "zip"
        if ext == ".pdf":
            return "pdf"
        if ext in IMG_EXTS:
            return "img"
        return None

    def run(self) -> None:
        try:
            count = 0
            err_count = 0
            dir_count = 0
            root = self.root_path

            def _onerr(e: OSError):
                nonlocal err_count
                err_count += 1
                # 例: [Errno 5] Access is denied: '\\\\192...'
                self.signals.progress.emit(f"walk error({err_count}): {e}")

            for dirpath, dirnames, filenames in os.walk(root, onerror=_onerr):
                dir_count += 1
                if dir_count % 50 == 0:
                    self.signals.progress.emit(f"スキャン中… dirs={dir_count} files={count}")

                # ---- dirs を登録（本が無いフォルダも棚に出すため） ----
                try:
                    rel_dir = os.path.relpath(dirpath, root).replace("/", "\\")
                    if rel_dir == ".":
                        rel_dir = ""
                    parent_dir = os.path.dirname(rel_dir)
                    if parent_dir == ".":
                        parent_dir = ""
                    name = os.path.basename(rel_dir) if rel_dir else ""
                    st_dir = os.stat(dirpath)
                    self.db.upsert_dir(
                        root_id=self.root_id,
                        rel_dir=rel_dir,
                        parent_dir=parent_dir,
                        name=name,
                        mtime=int(st_dir.st_mtime),
                    )
                except OSError as e:
                    err_count += 1
                    if err_count % 50 == 1:
                        self.signals.progress.emit(f"dir stat error({err_count}): {e}")

                # ネットワーク/権限で dirnames が空にされるケースの観測用
                if (count % 400 == 0) and (count > 0):
                    self.signals.progress.emit(f"スキャン中… files={count}  dir={dirpath}")

                for fn in filenames:
                    full = os.path.join(dirpath, fn)
                    btype = self._classify(full)
                    if not btype:
                        continue
                    try:
                        st = os.stat(full)
                    except OSError as e:
                        err_count += 1
                        if err_count % 50 == 1:
                            self.signals.progress.emit(f"stat error({err_count}): {e}")
                        continue

                    rel = os.path.relpath(full, root).replace("/", "\\")
                    parent_dir = os.path.dirname(rel)
                    title = os.path.splitext(os.path.basename(full))[0]
                    self.db.upsert_book(
                        path=norm(full),
                        root_id=self.root_id,
                        rel_path=rel,
                        parent_dir=parent_dir,
                        btype=btype,
                        size=int(st.st_size),
                        mtime=int(st.st_mtime),
                        title=title
                    )
                    count += 1

                    if count % 400 == 0:
                        self.signals.progress.emit(f"スキャン中… {count} files / errors={err_count}")

            self.signals.finished.emit(count)
        except Exception as e:
            self.signals.error.emit(f"ScanJob fatal: {e}")


# -----------------------------
# Thumbnail generation
# -----------------------------
class ThumbSignals(QObject):
    ready = pyqtSignal(str)   # book path

class ThumbJob(QRunnable):
    def __init__(self, db: LibraryDB, book_path: str, cache_dir: str):
        super().__init__()
        self.db = db
        self.book_path = norm(book_path)
        self.cache_dir = cache_dir
        self.signals = ThumbSignals()

    def _cover_sig(self, info_row: sqlite3.Row) -> str:
        return f"v{THUMB_VER}|s{THUMB_SIZE}|t{info_row['mtime']}|z{info_row['size']}"

    def _thumb_path(self, cover_sig: str) -> str:
        h = sha1(self.book_path + "|" + cover_sig)
        return os.path.join(self.cache_dir, f"{h}.jpg")

    def _save_thumb(self, img: Image.Image, out_path: str) -> None:
        # 画像を縮小（アスペクト維持）
        img = img.convert("RGB")
        img.thumbnail((THUMB_SIZE, THUMB_SIZE))

        # 正方形キャンバスを作って中央に貼る（センタリング）
        bg = (30, 31, 34)  # だいたい #1e1f22 相当
        canvas = Image.new("RGB", (THUMB_SIZE, THUMB_SIZE), bg)
        x = (THUMB_SIZE - img.width) // 2
        y = (THUMB_SIZE - img.height) // 2
        canvas.paste(img, (x, y))
        tmp_path = out_path + f".tmp_{uuid.uuid4().hex}"
        canvas.save(tmp_path, "JPEG", quality=85, optimize=True)
        os.replace(tmp_path, out_path)

    def _make_from_image(self, out_path: str) -> None:
        with Image.open(self.book_path) as im:
            self._save_thumb(im, out_path)

    def _make_from_pdf(self, out_path: str) -> None:
        doc = fitz.open(self.book_path)
        try:
            page = doc.load_page(0)
            pix = page.get_pixmap(dpi=110)
            mode = "RGB" if pix.alpha == 0 else "RGBA"
            im = Image.frombytes(mode, [pix.width, pix.height], pix.samples)
            self._save_thumb(im, out_path)
        finally:
            doc.close()

    def _make_from_zip(self, out_path: str) -> None:
        with zipfile.ZipFile(self.book_path) as zf:
            names = [n for n in zf.namelist() if (not n.endswith("/")) and is_image_name(n)]
            if not names:
                raise RuntimeError("zip内に画像がありません")
            names.sort(key=natural_key)
            first = names[0]
            data = zf.read(first)
            with Image.open(io.BytesIO(data)) as im:
                self._save_thumb(im, out_path)

    def run(self) -> None:
        info = self.db.get_thumb_info(self.book_path)
        if not info:
            return

        cover_sig = self._cover_sig(info)
        out_path = self._thumb_path(cover_sig)
        ensure_dir(self.cache_dir)

        # 既に生成済み
        if info["cover_sig"] == cover_sig and info["cover_thumb_path"] and os.path.exists(info["cover_thumb_path"]):
            self.signals.ready.emit(self.book_path)
            return

        try:
            btype = info["type"]
            if btype == "img":
                self._make_from_image(out_path)
            elif btype == "pdf":
                self._make_from_pdf(out_path)
            elif btype == "zip":
                self._make_from_zip(out_path)
            self.db.set_thumb_ok(self.book_path, out_path, cover_sig)
        except Exception:
            self.db.set_thumb_fail(self.book_path, cover_sig)

        self.signals.ready.emit(self.book_path)


class ThumbManager(QObject):
    thumb_ready = pyqtSignal(str)
    status_changed = pyqtSignal(int, int)

    def __init__(self, db: LibraryDB, cache_dir: str, pool: QThreadPool):
        super().__init__()
        self.db = db
        self.cache_dir = cache_dir
        self.pool = pool
        self.inflight: Set[str] = set()
        self.running = 0
        self.queue = deque()
        self.queued: Set[str] = set()

    def request(self, path: str) -> None:
        path = norm(path)
        if path in self.inflight:
            return
        info = self.db.get_thumb_info(path)
        if not info:
            return
        if info["cover_state"] == 1 and info["cover_thumb_path"] and os.path.exists(info["cover_thumb_path"]):
            return

        if self.running < MAX_THUMB_JOBS:
            self._start_job(path)
            self._emit_status()
            return

        if path not in self.queued:
            self.queue.append(path)
            self.queued.add(path)
            self._emit_status()

    def _start_job(self, path: str) -> None:
        self.inflight.add(path)
        self.running += 1
        job = ThumbJob(self.db, path, self.cache_dir)
        job.signals.ready.connect(self._done)
        self.pool.start(job)

    def _done(self, path: str) -> None:
        path = norm(path)
        self.inflight.discard(path)
        self.running = max(0, self.running - 1)
        self.thumb_ready.emit(path)

        while self.running < MAX_THUMB_JOBS and self.queue:
            nxt = self.queue.popleft()
            self.queued.discard(nxt)
            if nxt in self.inflight:
                continue
            info = self.db.get_thumb_info(nxt)
            if not info:
                continue
            if info["cover_state"] == 1 and info["cover_thumb_path"] and os.path.exists(info["cover_thumb_path"]):
                continue
            self._start_job(nxt)
        
        self._emit_status()

    def clear_queue(self):
        self.queue.clear()
        self.queued.clear()
        self._emit_status()

    def _emit_status(self):
        self.status_changed.emit(len(self.queue), self.running)

    def retry_broken(self, path: str):
        self.db.set_thumb_fail(path, "")
        self.request(path)

class IconCache:
    def __init__(self):
        self._cache: Dict[str, QIcon] = {}

    def icon_for(self, thumb_path: Optional[str], rating: int = 0) -> QIcon:
        if not thumb_path or not os.path.exists(thumb_path):
            return QIcon()

        key = f"{thumb_path}|r{int(rating)}"
        if key in self._cache:
            return self._cache[key]

        pm0 = QPixmap(thumb_path)
        if pm0.isNull():
            return QIcon()

        base = pm0.scaled(
            QSize(180, 180),
            Qt.AspectRatioMode.KeepAspectRatio,
            Qt.TransformationMode.SmoothTransformation
        )

        # ★の有無に関係なく「キャンバスに中央貼り」
        pm = QPixmap(180, 180)
        pm.fill(Qt.GlobalColor.transparent)

        p = QPainter(pm)
        p.setRenderHint(QPainter.RenderHint.Antialiasing, True)

        x = (180 - base.width()) // 2
        y = (180 - base.height()) // 2
        p.drawPixmap(x, y, base)

        # ★バッジは rating>0 のときだけ
        if int(rating) > 0:
            text = "★"
            p.setFont(QFont("Segoe UI", 18, QFont.Weight.Bold))

            # 読みやすくするため背景を薄く敷く（角丸）
            badge_w, badge_h = 38, 30
            bx, by = 180 - badge_w - 6, 180 - badge_h - 6
            p.setBrush(Qt.GlobalColor.black)
            p.setOpacity(0.55)
            p.setPen(Qt.PenStyle.NoPen)
            p.drawRoundedRect(QRect(bx, by, badge_w, badge_h), 8, 8)

            p.setOpacity(1.0)
            p.setPen(Qt.GlobalColor.white)
            p.drawText(QRect(bx, by, badge_w, badge_h), Qt.AlignmentFlag.AlignCenter, text)

        p.end()

        ic = QIcon(pm)
        self._cache[key] = ic
        return ic

    def drop(self, thumb_path: Optional[str]) -> None:
        if not thumb_path:
            return
        # rating違いも全部落とす
        dels = [k for k in self._cache.keys() if k.startswith(thumb_path + "|")]
        for k in dels:
            self._cache.pop(k, None)


# -----------------------------
# Models
# -----------------------------
@dataclass
class BookItem:
    path: str
    title: str
    rel_path: str
    rating: int

@dataclass
class FolderItem:
    child: str
    rep_path: str
    rating: int

# 混在ビュー用（dirカード + 直下book）
@dataclass
class MixedItem:
    kind: str            # "dir" or "book"
    title: str
    tooltip: str
    rel_dir: str = ""    # kind=="dir"
    rep_path: str = ""   # kind=="dir"（代表表紙のパス。無ければ空）
    path: str = ""       # kind=="book"
    rel_path: str = ""   # kind=="book"
    rating: int = 0


class BookListModel(QAbstractListModel):
    def __init__(self, db: LibraryDB, thumb: ThumbManager, icons: IconCache):
        super().__init__()
        self.db = db
        self.thumb = thumb
        self.icons = icons
        self.items: List[BookItem] = []

    def rowCount(self, parent=QModelIndex()) -> int:
        return len(self.items)

    def data(self, index: QModelIndex, role: int):
        if not index.isValid():
            return None
        item = self.items[index.row()]

        if role == Qt.ItemDataRole.DisplayRole:
            star = "★ " if int(item.rating) > 0 else ""
            return f"{star}{item.title}"
        if role == Qt.ItemDataRole.ToolTipRole:
            return f"{item.rel_path}\nRating: {item.rating}"
        if role == Qt.ItemDataRole.DecorationRole:
            info = self.db.get_thumb_info(item.path)
            if info and info["cover_state"] == 1:
                ic = self.icons.icon_for(info["cover_thumb_path"], item.rating)
                if ic.isNull():
                    self.icons.drop(info["cover_thumb_path"])
                    self.thumb.retry_broken(item.path)
                    return QIcon()
                return ic
            # ここで “必要になった分だけ” 生成要求
            self.thumb.request(item.path)
            return QIcon()
        return None

    def set_items(self, items: List[BookItem]) -> None:
        self.beginResetModel()
        self.items = items
        self.endResetModel()

    def notify_thumb_ready(self, path: str) -> None:
        # 互換のため残す（旧呼び出し対策）
        self.notify_thumb_ready_hit(path)

    def notify_thumb_ready_hit(self, path: str) -> bool:
        # 該当行だけ再描画（見つかったら True）
        for i, it in enumerate(self.items):
            if it.path == path:
                idx = self.index(i)
                self.dataChanged.emit(idx, idx, [Qt.ItemDataRole.DecorationRole])
                return True
        return False


class FolderListModel(QAbstractListModel):
    def __init__(self, db: LibraryDB, thumb: ThumbManager, icons: IconCache):
        super().__init__()
        self.db = db
        self.thumb = thumb
        self.icons = icons
        self.items: List[FolderItem] = []

    def rowCount(self, parent=QModelIndex()) -> int:
        return len(self.items)

    def data(self, index: QModelIndex, role: int):
        if not index.isValid():
            return None
        item = self.items[index.row()]

        if role == Qt.ItemDataRole.DisplayRole:
            star = "★ " if int(item.rating) > 0 else ""
            name = "(このフォルダの本)" if item.child == "." else item.child
            return f"{star}{name}"
        if role == Qt.ItemDataRole.ToolTipRole:
            return f"{item.rep_path}\nRating: {item.rating}"
        if role == Qt.ItemDataRole.DecorationRole:
            info = self.db.get_thumb_info(item.rep_path)
            if info and info["cover_state"] == 1:
                ic = self.icons.icon_for(info["cover_thumb_path"], item.rating)
                if ic.isNull():
                    self.icons.drop(info["cover_thumb_path"])
                    self.thumb.retry_broken(item.rep_path)
                    return QIcon()
                return ic
            self.thumb.request(item.rep_path)
            return QIcon()
        return None

    def set_items(self, items: List[FolderItem]) -> None:
        self.beginResetModel()
        self.items = items
        self.endResetModel()

    def notify_thumb_ready(self, rep_path: str) -> None:
        # 互換のため残す
        self.notify_thumb_ready_hit(rep_path)

    def notify_thumb_ready_hit(self, rep_path: str) -> bool:
        for i, it in enumerate(self.items):
            if it.rep_path == rep_path:
                idx = self.index(i)
                self.dataChanged.emit(idx, idx, [Qt.ItemDataRole.DecorationRole])
                return True
        return False

class MixedListModel(QAbstractListModel):
    def __init__(self, db: LibraryDB, thumb: ThumbManager, icons: IconCache):
        super().__init__()
        self.db = db
        self.thumb = thumb
        self.icons = icons
        self.items: List[MixedItem] = []

    def rowCount(self, parent=QModelIndex()) -> int:
        return len(self.items)

    def data(self, index: QModelIndex, role: int):
        if not index.isValid():
            return None
        item = self.items[index.row()]

        if role == Qt.ItemDataRole.DisplayRole:
            star = "★ " if int(item.rating) > 0 else ""
            label = item.title
            if item.kind == "dir":
                label = f"📁 {label}"
            return f"{star}{label}"

        if role == Qt.ItemDataRole.ToolTipRole:
            return f"{item.tooltip}\nRating: {item.rating}"

        if role == Qt.ItemDataRole.DecorationRole:
            if item.kind == "dir":
                if not item.rep_path:
                    return QIcon()
                info = self.db.get_thumb_info(item.rep_path)
                if info and info["cover_state"] == 1:
                    ic = self.icons.icon_for(info["cover_thumb_path"], item.rating)
                    if ic.isNull():
                        self.icons.drop(info["cover_thumb_path"])
                        self.thumb.retry_broken(item.rep_path)
                        return QIcon()
                    return ic
                self.thumb.request(item.rep_path)
                return QIcon()

            # book
            info = self.db.get_thumb_info(item.path)
            if info and info["cover_state"] == 1:
                ic = self.icons.icon_for(info["cover_thumb_path"], item.rating)
                if ic.isNull():
                    self.icons.drop(info["cover_thumb_path"])
                    self.thumb.retry_broken(item.path)
                    return QIcon()
                return ic
            self.thumb.request(item.path)
            return QIcon()

        return None

    def set_items(self, items: List[MixedItem]) -> None:
        self.beginResetModel()
        self.items = items
        self.endResetModel()

    def notify_thumb_ready(self, path: str) -> None:
        # 互換のため残す
        self.notify_thumb_ready_hit(path)

    def notify_thumb_ready_hit(self, path: str) -> bool:
        for i, it in enumerate(self.items):
            if (it.kind == "book" and it.path == path) or (it.kind == "dir" and it.rep_path == path):
                idx = self.index(i)
                self.dataChanged.emit(idx, idx, [Qt.ItemDataRole.DecorationRole])
                return True
        return False

# -----------------------------
# Main Window
# -----------------------------
class MainWindow(QMainWindow):
    def __init__(self, db: LibraryDB, cache_dir: str):
        super().__init__()
        self.db = db
        self.pool = QThreadPool.globalInstance()
        self.cache_dir = cache_dir
        self.settings = QSettings(APP_NAME, "Settings")

        self.icons = IconCache()
        self.thumb = ThumbManager(self.db, self.cache_dir, self.pool)
        self.thumb.thumb_ready.connect(self._on_thumb_ready)
        
        # ---- 追加：サムネ完了通知の取りこぼし救済（全体Decoration更新を合成して1回にまとめる） ----
        self._deco_refresh_pending = False
        self._deco_refresh_timer = QTimer(self)
        self._deco_refresh_timer.setSingleShot(True)
        self._deco_refresh_timer.timeout.connect(self._emit_deco_refresh_all)

        # フォルダ移動後の自動「再描画」(デバウンス付き)
        self._auto_redraw_timer = QTimer(self)
        self._auto_redraw_timer.setSingleShot(True)
        self._auto_redraw_timer.timeout.connect(self.force_redraw_visible)

        self.auto_redraw_enabled = True  # 必要なら設定化

        self.thumb_status_lbl = QLabel("Thumb: -")
        self.statusBar().addPermanentWidget(self.thumb_status_lbl)
        self.thumb.status_changed.connect(self._update_thumb_status)

        self.root_path: Optional[str] = None
        self.root_id: Optional[int] = None
        self.current_dir_rel = ""   # "" がルート
        self._scroll_pos = {}  # key: (dir_rel, mode_index) -> (scroll_val, anchor)
        self._scan_running = False
        self._scan_job = None

        self.setWindowTitle(f"{APP_NAME} (Bookshelf.py)")

        central = QWidget()
        self.setCentralWidget(central)
        v = QVBoxLayout(central)

        top = QHBoxLayout()
        v.addLayout(top)

        self.btn_back = QPushButton("←")
        self.btn_up = QPushButton("↑")
        top.addWidget(self.btn_back, 0)
        top.addWidget(self.btn_up, 0)

        self.root_display = QLineEdit()
        self.root_display.setReadOnly(True)
        self.root_display.setPlaceholderText("ルート未選択")
        top.addWidget(self.root_display, 2)

        self.search = QLineEdit()
        self.search.setPlaceholderText("検索（タイトル/パス）")
        top.addWidget(self.search, 2)

        # 棚/フラットは2択なのでトグルにする（OFF=棚, ON=フラット）
        self.btn_mode = QPushButton("棚（混在）")
        self.btn_mode.setCheckable(True)
        self.btn_mode.setChecked(False)
        self.btn_mode.toggled.connect(self._on_mode_toggled)
        top.addWidget(self.btn_mode, 0)
        QShortcut(QKeySequence("F"), self, activated=self.btn_mode.toggle)

        self.btn_only_star = QPushButton("全て")
        self.btn_only_star.setCheckable(True)
        self.btn_only_star.setChecked(False)
        self.btn_only_star.toggled.connect(self._on_star_filter_toggled)
        top.addWidget(self.btn_only_star, 0)

        QShortcut(QKeySequence("S"), self, activated=self.btn_only_star.toggle)

        self.btn_root = QPushButton("ルート選択")
        top.addWidget(self.btn_root, 0)
        
        self.btn_scan = QPushButton("スキャン")
        top.addWidget(self.btn_scan, 0)
        
        self.btn_redraw = QPushButton("再描画")
        top.addWidget(self.btn_redraw, 0)
        
        self.btn_open = QPushButton("外部で開く")
        top.addWidget(self.btn_open, 0)
        
        self.setStatusBar(self.statusBar())

        self.view = QListView()
        self.view.setViewMode(QListView.ViewMode.IconMode)
        self.view.setResizeMode(QListView.ResizeMode.Adjust)
        self.view.setIconSize(QSize(220, 220))
        self.view.setGridSize(QSize(245, 300))
        self.view.setWordWrap(True)
        self.view.setTextElideMode(Qt.TextElideMode.ElideRight)
        self.view.setUniformItemSizes(True)
        self.view.setWrapping(True)
        self.view.setFlow(QListView.Flow.LeftToRight)
        self.view.setSpacing(6)

        # --- 選択を確実にする（★トグルの前提） ---
        self.view.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.view.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectItems)
        self.view.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        # 左クリックで currentIndex を必ず更新（余白クリック等のブレを減らす）
        self.view.clicked.connect(self.view.setCurrentIndex)

        self.view.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.view.customContextMenuRequested.connect(self._on_view_context_menu)
        v.addWidget(self.view, 1)

        self.book_model = BookListModel(self.db, self.thumb, self.icons)
        self.folder_model = FolderListModel(self.db, self.thumb, self.icons)  # 未使用（互換）
        self.mixed_model = MixedListModel(self.db, self.thumb, self.icons)

        self.btn_root.clicked.connect(self.choose_root)
        self.btn_scan.clicked.connect(self.scan)
        self.btn_redraw.clicked.connect(self.force_redraw_visible)
        self.search.textChanged.connect(self.refresh)
        self.btn_open.clicked.connect(self.open_external)
        self.btn_back.clicked.connect(self.nav_back)
        self.btn_up.clicked.connect(self.nav_up)
        self.view.doubleClicked.connect(self._on_item_activated)
        
        self.view.verticalScrollBar().valueChanged.connect(lambda _: QTimer.singleShot(0, self._prefetch_visible))
        self.view.horizontalScrollBar().valueChanged.connect(lambda _: QTimer.singleShot(0, self._prefetch_visible))

        # チルト（戻るボタン）をリストビュー上でも検知するためのフィルター
        self.view.installEventFilter(self)
        self.view.viewport().installEventFilter(self)

        # 起動時のルート復元（QSettings優先 -> DB履歴）
        last_root = self.settings.value("last_root", "")
        last_dir = self.settings.value("last_dir", "")

        if last_root and os.path.exists(last_root):
            self.root_path = norm(last_root)
            self.root_id = self.db.upsert_root(self.root_path)
            self.current_dir_rel = last_dir if last_dir else ""
            self.root_display.setText(self.root_path)
            self.setWindowTitle(f"{APP_NAME} (Bookshelf.py)  —  {self.root_path}")
            self.statusBar().showMessage(f"ROOT: {self.root_path}")
            self.refresh()
            
            self.thumb.clear_queue()
            QTimer.singleShot(0, self._prefetch_visible)
            QTimer.singleShot(120, self._prefetch_visible)
        else:
            roots = self.db.get_roots()
            if roots:
                self.set_root(roots[0])

    def _selected_item(self):
        """
        returns:
          ("book", abs_path, None) or ("dir", abs_dir_path, rel_dir) or (None, None, None)
        """
        idx = self.view.currentIndex()
        if not idx.isValid():
            return (None, None, None)
        model = self.view.model()
        if model is None or not hasattr(model, "items"):
            return (None, None, None)
        row = idx.row()
        if row < 0 or row >= len(model.items):
            return (None, None, None)
        item = model.items[row]

        # Mixed: dir/book
        if hasattr(item, "kind"):
            if item.kind == "dir":
                abs_dir = self._abs_dir(item.rel_dir)
                return ("dir", abs_dir, item.rel_dir)
            return ("book", item.path, None)

        # BookListModel: book only
        if hasattr(item, "path"):
            return ("book", item.path, None)

        return (None, None, None)

    def choose_root(self):
        default_dir = r"\\192.168.24.202\Books"
        path = QFileDialog.getExistingDirectory(self, "ルートフォルダを選択", default_dir)
        if path:
            self.set_root(path)

    def set_root(self, path: str):
        self.root_path = norm(path)
        self.root_id = self.db.upsert_root(self.root_path)
        self.current_dir_rel = ""
        self._scroll_pos.clear()
        
        self.settings.setValue("last_root", self.root_path)
        self.settings.setValue("last_dir", "")

        self.root_display.setText(self.root_path)
        self.setWindowTitle(f"{APP_NAME} (Bookshelf.py)  —  {self.root_path}")
        self.statusBar().showMessage(f"ROOT: {self.root_path}")
        self.refresh()
        
        self.thumb.clear_queue()
        QTimer.singleShot(0, self._prefetch_visible)
        QTimer.singleShot(120, self._prefetch_visible)

        self._schedule_auto_redraw(1000)

    def _mode_index(self) -> int:
        # 0 = 棚（混在）, 1 = フラット（配下すべて）
        return 1 if self.btn_mode.isChecked() else 0

    def _on_mode_toggled(self, checked: bool):
        self.btn_mode.setText("フラット（配下すべて）" if checked else "棚（混在）")
        self.refresh()

    def _only_star(self) -> bool:
        return self.btn_only_star.isChecked()

    def _on_star_filter_toggled(self, checked: bool):
        self.btn_only_star.setText("★のみ" if checked else "全て")
        self.refresh()

    def _update_thumb_status(self, q, r):
        self.thumb_status_lbl.setText(f"Thumb: Q={q} Run={r}")
        # 止まったら念のため画面内を再チェック（軽い保険）
        if r == 0 and q == 0:
            QTimer.singleShot(200, self._prefetch_visible)

    def _schedule_deco_refresh_all(self, delay_ms: int = 60):
        if self._deco_refresh_pending:
            return
        self._deco_refresh_pending = True
        self._deco_refresh_timer.start(delay_ms)

    def _emit_deco_refresh_all(self):
        self._deco_refresh_pending = False
        model = self.view.model()
        if model is None:
            return
        try:
            rc = model.rowCount()
            if rc > 0:
                tl = model.index(0, 0)
                br = model.index(rc - 1, 0)
                model.dataChanged.emit(tl, br, [Qt.ItemDataRole.DecorationRole])
        finally:
            self.view.viewport().update()

    def force_redraw_visible(self):
        self.statusBar().showMessage("再描画: 要求再発行...", 1000)
        model = self.view.model()
        if model is None:
            return

        # いまの画面に関係ないキューが詰まってると「止まった」ように見えるので掃除
        self.thumb.clear_queue()
        self.view.doItemsLayout()          # これ追加

        # 可視アイテムに対してサムネ要求を確実に再発行
        self._prefetch_visible()

        # Qtに「装飾を取り直せ」と強制（DecorationRole再評価）
        try:
            if model.rowCount() > 0:
                top_left = model.index(0, 0)
                bottom_right = model.index(model.rowCount() - 1, 0)
                model.dataChanged.emit(top_left, bottom_right, [Qt.ItemDataRole.DecorationRole])
        except Exception:
            pass

        # 念のため再描画
        self.view.viewport().update()

        # レイアウト確定後にももう一回（これが効くケースがある）
        QTimer.singleShot(150, self._prefetch_visible)
        QTimer.singleShot(150, self.view.viewport().update)

    def scan(self):
        if not self.root_path or not self.root_id:
            QMessageBox.information(self, "Info", "先にルートを選択してね")
            return

        self._scan_running = True
        self.statusBar().showMessage("スキャン開始…")

        job = ScanJob(self.db, self.root_id, self.root_path)
        self._scan_job = job

        def on_progress(msg: str):
            self.statusBar().showMessage(msg)

        def on_finished(c: int):
            self._scan_running = False
            self.refresh()
            QTimer.singleShot(0, lambda: self.statusBar().showMessage(f"スキャン完了: {c} files"))

        def on_error(e: str):
            self._scan_running = False
            QMessageBox.critical(self, "Scan Error", e)

        job.signals.progress.connect(on_progress)
        job.signals.finished.connect(on_finished)
        job.signals.error.connect(on_error)

        self.pool.start(job)

    def refresh(self):
        if not self.root_id:
            return
        
        self.settings.setValue("last_dir", self.current_dir_rel)

        # Update UI for current location
        crumb = self._crumb()
        self.setWindowTitle(f"{APP_NAME} (Bookshelf.py) — {crumb}")
        self.root_display.setText(crumb)

        q = self.search.text()
        star = self._only_star()

        if self._mode_index() == 1:
            # フラット（配下すべて）
            rows = self.db.list_books_recursive(self.root_id, self.current_dir_rel, query=q, only_star=star)
            items = [BookItem(path=r["path"], title=r["title"], rel_path=r["rel_path"], rating=int(r["rating"])) for r in rows]
            self.book_model.set_items(items)
            self.view.setModel(self.book_model)
            if not self._scan_running:
                status = "フラット" + (" (★のみ)" if star else "")
                self.statusBar().showMessage(f"{status}: {len(items)}  (ROOT: {self._crumb()})")
            # 直後はレイアウト未確定があるので、少し遅延して確実にprefetch
            QTimer.singleShot(0, self.view.doItemsLayout)
            QTimer.singleShot(60, self._restore_scroll)
            QTimer.singleShot(140, self._prefetch_visible)
            QTimer.singleShot(260, self._prefetch_visible)
            return

        # ---- 混在ビュー：子フォルダカード + 直下の本 ----
        dir_rows = self.db.list_child_dirs(self.root_id, parent_dir=self.current_dir_rel, query=q)
        # 棚（混在）：
        #  - ★なし: 直下の本を全部
        #  - ★のみ: 直下の★本だけ（フォルダも★条件で残す）
        book_rows = self.db.list_direct_books(self.root_id, dir_rel=self.current_dir_rel, query=q, only_star=star)

        items: List[MixedItem] = []

        dir_items: List[MixedItem] = []
        for d in dir_rows:
            rel_dir = d["rel_dir"]
            name = d["name"]
            # 代表表紙は★フィルタに左右されない（棚の見た目を安定させる）→ ★のみ時は★本を代表にする
            rep_info = self.db.get_dir_rep_path(self.root_id, rel_dir, only_star=star)
            rep_path = rep_info[0] if rep_info else ""
            # フォルダの★はフォルダ自身（絶対パス）に付与する
            dir_abs = self._abs_dir(rel_dir)
            dir_star = self.db.get_rating(dir_abs)

            has_star_book = False
            if star:
                has_star_book = self.db.dir_has_star_books(self.root_id, rel_dir)

            # 「★のみ」のときは★付きフォルダ または 配下に★本があるフォルダ だけ表示
            if star and (dir_star <= 0 and not has_star_book):
                continue

            dir_items.append(MixedItem(
                kind="dir",
                title=name if name else "(root)",
                tooltip=self._crumb_for(rel_dir),
                rel_dir=rel_dir,
                rep_path=rep_path,
                rating=int(dir_star)
            ))

        book_items: List[MixedItem] = []
        for r in book_rows:
            book_items.append(MixedItem(
                kind="book",
                title=r["title"],
                tooltip=r["rel_path"],
                path=r["path"],
                rel_path=r["rel_path"],
                rating=int(r["rating"])
            ))

        if SHOW_DIRS_FIRST:
            items = dir_items + book_items
        else:
            items = book_items + dir_items

        self.mixed_model.set_items(items)
        self.view.setModel(self.mixed_model)

        if not self._scan_running:
            status = "棚（混在）" + (" (★のみ)" if star else "")
            self.statusBar().showMessage(f"{status}: dirs={len(dir_items)} books={len(book_items)}  (ROOT: {self._crumb()})")

        # 直後はレイアウト未確定があるので、少し遅延して確実にprefetch
        QTimer.singleShot(0, self.view.doItemsLayout)
        QTimer.singleShot(60, self._restore_scroll)
        QTimer.singleShot(140, self._prefetch_visible)
        QTimer.singleShot(260, self._prefetch_visible)

        # ここでは全件サムネ要求を投げない（クラッシュ原因）
        # 表示時のDecorationRoleで必要分だけ要求される

    def _selected_book_path(self) -> Optional[str]:
        kind, path, _rel = self._selected_item()
        return path if kind == "book" else None

    def toggle_star(self):
        kind, path, rel_dir = self._selected_item()
        if not kind or not path:
            return

        cur = self.db.get_rating(path)
        new = 0 if cur > 0 else 1
        self.db.set_rating(path, new)

        # book はサムネバッジ更新が必要。dir は代表サムネは同じなので icons クリアは不要
        if kind == "book":
            info = self.db.get_thumb_info(path)
            thumb_path = info["cover_thumb_path"] if info else None
            self.icons.drop(thumb_path)

        self.refresh()

    def open_external(self):
        path = self._selected_book_path()
        if not path:
            return
        self._open_in_honeyview(path)

    def _open_in_honeyview(self, path: str) -> None:
        if not os.path.exists(VIEWER_EXE):
            QMessageBox.critical(self, "Viewer Error", f"Honeyview が見つからない:\n{VIEWER_EXE}")
            return
        try:
            subprocess.Popen([VIEWER_EXE, path], shell=False)
        except Exception as e:
            QMessageBox.critical(self, "Viewer Error", f"起動に失敗:\n{e}")

    def _on_view_context_menu(self, pos):
        idx = self.view.indexAt(pos)
        if idx.isValid():
            self.view.setCurrentIndex(idx)

        kind, sel_path, sel_rel_dir = self._selected_item()
        if not kind or not sel_path:
            return

        menu = QMenu(self)

        if kind == "dir":
            act_enter = QAction("このフォルダに入る", self)
            act_enter.triggered.connect(lambda: self._enter_dir(sel_rel_dir))
            menu.addAction(act_enter)

            act_open_folder = QAction("エクスプローラーでフォルダを開く", self)
            act_open_folder.triggered.connect(lambda: self._open_folder(self._abs_dir(sel_rel_dir)))
            menu.addAction(act_open_folder)
            menu.addSeparator()

            # フォルダ★（棚用）
            cur = self.db.get_rating(self._abs_dir(sel_rel_dir))
            act_star_dir = QAction("★を外す" if cur > 0 else "★を付ける", self)
            act_star_dir.triggered.connect(self.toggle_star)
            menu.addAction(act_star_dir)
            menu.addSeparator()
        else:
            # book
            cur = self.db.get_rating(sel_path)
            act_star = QAction("★を外す" if cur > 0 else "★を付ける", self)
            act_star.triggered.connect(self.toggle_star)
            menu.addAction(act_star)
            menu.addSeparator()

            act_open = QAction("Honeyviewで開く", self)
            act_open.triggered.connect(lambda: self._open_in_honeyview(sel_path))
            menu.addAction(act_open)

            act_select = QAction("エクスプローラーでファイルを選択", self)
            act_select.triggered.connect(lambda: self._select_in_explorer(sel_path))
            menu.addAction(act_select)
            menu.addSeparator()

        menu.exec(self.view.viewport().mapToGlobal(pos))

    def _enter_dir(self, rel_dir: str):
        self._save_scroll()
        self.current_dir_rel = rel_dir
        self.refresh()
        # フォルダ移動直後はレイアウト未確定で可視判定が漏れることがあるので保険を打つ
        self.thumb.clear_queue()
        QTimer.singleShot(0, self._prefetch_visible)
        QTimer.singleShot(120, self._prefetch_visible)
        self._schedule_auto_redraw(1000)

    def _open_folder(self, folder: str) -> None:
        try:
            subprocess.Popen(["explorer", folder], shell=False)
            threading.Thread(target=self._send_scroll_keys, daemon=True).start()
        except Exception as e:
            QMessageBox.critical(self, "Explorer Error", f"フォルダを開けない:\n{e}")

    def _send_scroll_keys(self):
        time.sleep(0.5)
        ctypes.windll.user32.keybd_event(0x28, 0, 0, 0)  # VK_DOWN
        ctypes.windll.user32.keybd_event(0x28, 0, 2, 0)
        time.sleep(0.05)
        ctypes.windll.user32.keybd_event(0x26, 0, 0, 0)  # VK_UP
        ctypes.windll.user32.keybd_event(0x26, 0, 2, 0)

    def _select_in_explorer(self, path: str) -> None:
        try:
            subprocess.Popen(["explorer", "/select,", path], shell=False)
            threading.Thread(target=self._send_scroll_keys, daemon=True).start()
        except Exception as e:
            QMessageBox.critical(self, "Explorer Error", f"選択表示できない:\n{e}")

    def _on_thumb_ready(self, path: str) -> None:
        # 現在のモデルに通知して、該当行だけ再描画
        model = self.view.model()
        hit = False
        if isinstance(model, BookListModel):
            hit = model.notify_thumb_ready_hit(path)
        elif isinstance(model, FolderListModel):
            hit = model.notify_thumb_ready_hit(path)
        elif isinstance(model, MixedListModel):
            hit = model.notify_thumb_ready_hit(path)
        
        self.view.viewport().update()

        # 取りこぼし救済：完了通知が「いま表示中のモデル」にいない場合がある
        # そのときは少し遅らせて全体のDecorationRole再評価を1回だけ入れる（連発は合成）
        if not hit:
            self._schedule_deco_refresh_all()

    def _prefetch_visible(self, _try=0):
        model = self.view.model()
        if model is None or model.rowCount() <= 0:
            return

        vp_rect = self.view.viewport().rect()

        top_idx = self.view.indexAt(QPoint(vp_rect.left() + 2, vp_rect.top() + 2))
        if not top_idx.isValid():
            # レイアウトが固まるまで最大20回だけ粘る
            if _try < 20:
                QTimer.singleShot(80, lambda: self._prefetch_visible(_try + 1))
            return

        bottom_idx = self.view.indexAt(QPoint(vp_rect.right() - 2, vp_rect.bottom() - 2))
        last_row = bottom_idx.row() if bottom_idx.isValid() else min(model.rowCount() - 1, top_idx.row() + 60)

        first_row = max(0, top_idx.row() - 10)
        last_row = min(model.rowCount() - 1, last_row + 30)

        for row in range(first_row, last_row + 1):
            item = model.items[row]
            p = getattr(item, "path", None) or getattr(item, "rep_path", None)
            if p:
                self.thumb.request(p)

    def _rep_path_for_current(self) -> str:
        rows = self.db.list_books(self.root_id, query="", only_star=False, dir_rel=self.current_dir_rel)
        return rows[0]["path"] if rows else (self.root_path or "")

    def _crumb(self) -> str:
        if not self.root_path:
            return ""
        if not self.current_dir_rel:
            return self.root_path
        return self.root_path + "\\" + self.current_dir_rel

    def _crumb_for(self, rel_dir: str) -> str:
        if not self.root_path:
            return ""
        return self.root_path + ("\\" + rel_dir if rel_dir else "")

    def _abs_dir(self, rel_dir: str) -> str:
        if not self.root_path:
            return ""
        return norm(os.path.join(self.root_path, rel_dir)) if rel_dir else self.root_path

    def nav_into(self, child: str):
        if not child or child == ".":
            return
        self._save_scroll()
        self.current_dir_rel = child if not self.current_dir_rel else (self.current_dir_rel + "\\" + child)
        self.refresh()
        self._schedule_auto_redraw(1000)

    def nav_up(self):
        if not self.current_dir_rel:
            return
        self._save_scroll()
        self.current_dir_rel = os.path.dirname(self.current_dir_rel)
        if self.current_dir_rel == ".":
            self.current_dir_rel = ""
        self.refresh()
        self.thumb.clear_queue()
        QTimer.singleShot(0, self._prefetch_visible)
        QTimer.singleShot(120, self._prefetch_visible)
        self._schedule_auto_redraw(1000)

    def _save_scroll(self):
        key = (self.current_dir_rel, self._mode_index())
        val = self.view.verticalScrollBar().value()
        anchor = None
        
        idx = self.view.indexAt(self.view.viewport().rect().topLeft())
        if idx.isValid():
            model = self.view.model()
            if model and idx.row() < model.rowCount():
                item = model.items[idx.row()]
                if hasattr(item, "kind"):
                    anchor = ("dir", item.rel_dir) if item.kind == "dir" else ("book", item.path)
                elif hasattr(item, "path"):
                    anchor = ("book", item.path)
        
        self._scroll_pos[key] = (val, anchor)

    def _restore_scroll(self):
        key = (self.current_dir_rel, self._mode_index())
        data = self._scroll_pos.get(key)
        if not data:
            return
        
        bar_val, anchor = data
        model = self.view.model()
        if not model:
            return

        target_row = None
        if anchor:
            kind, idv = anchor
            for i, item in enumerate(model.items):
                if hasattr(item, "kind"):
                    if kind == "dir" and item.kind == "dir" and item.rel_dir == idv:
                        target_row = i
                        break
                    if kind == "book" and item.kind == "book" and item.path == idv:
                        target_row = i
                        break
                elif hasattr(item, "path"):
                    if kind == "book" and item.path == idv:
                        target_row = i
                        break
        
        if target_row is not None:
            idx = model.index(target_row, 0)
            QTimer.singleShot(0, lambda: self.view.scrollTo(idx, QAbstractItemView.ScrollHint.PositionAtTop))
        else:
            QTimer.singleShot(0, lambda: self.view.verticalScrollBar().setValue(bar_val))

    def nav_back(self):
        self.nav_up()

    def _schedule_auto_redraw(self, delay_ms: int = 500):
        if not getattr(self, "auto_redraw_enabled", True):
            return
        # 連続移動時は最後の1回だけにする
        self._auto_redraw_timer.stop()
        self._auto_redraw_timer.start(delay_ms)

    def _on_item_activated(self, index: QModelIndex):
        model = self.view.model()
        if not index.isValid() or model is None:
            return

        if isinstance(model, MixedListModel):
            it = model.items[index.row()]
            if it.kind == "dir":
                self._enter_dir(it.rel_dir)
            else:
                self._open_in_honeyview(it.path)
            return

        if isinstance(model, BookListModel):
            it = model.items[index.row()]
            self._open_in_honeyview(it.path)
            return

        if isinstance(model, FolderListModel):
            it = model.items[index.row()]
            self.nav_into(it.child)

    def wheelEvent(self, event: QWheelEvent):
        """Handle wheel events, especially horizontal tilt for navigation."""
        # This event is processed if child widgets (like QListView) don't handle it.
        # QListView handles vertical scroll, but ignores horizontal scroll (tilt),
        # so the event propagates up to the main window.
        
        delta_x = event.angleDelta().x()
        delta_y = event.angleDelta().y()
        mods = event.modifiers()

        # Left Tilt (x > 0) or Shift+ScrollUp (y > 0) -> Back
        if delta_x > 0 or ((mods & Qt.KeyboardModifier.ShiftModifier) and delta_y > 0):
            self.nav_back()
            event.accept()
        # Right Tilt (x < 0) or Shift+ScrollDown (y < 0) -> Ignore
        elif delta_x < 0 or ((mods & Qt.KeyboardModifier.ShiftModifier) and delta_y < 0):
            event.accept()
        else:
            event.ignore()

    def eventFilter(self, source, event: QEvent):
        """リストビュー上でのマウス操作を監視"""
        if (source is self.view or source is self.view.viewport()) and event.type() == QEvent.Type.MouseButtonPress:
            # XButton1 はチルト左 / 戻るボタン
            if event.button() == Qt.MouseButton.XButton1:
                self.nav_back()
                return True  # イベントを消費
        return super().eventFilter(source, event)

    def mousePressEvent(self, event: QMouseEvent):
        """
        ウィンドウの余白などでチルトした場合の処理。
        eventFilterで拾えない部分を補完する。
        """
        if event.button() == Qt.MouseButton.XButton1:
            self.nav_back()
            event.accept()
        else:
            super().mousePressEvent(event)

def main():
    app = QApplication(sys.argv)

    app.setStyleSheet("""
    QWidget {
      background: #1e1f22;
      color: #e6e6e6;
      font-size: 10pt;
    }
    QLineEdit, QComboBox {
      background: #2b2d31;
      border: 1px solid #3a3d44;
      border-radius: 8px;
      padding: 6px 8px;
    }
    QPushButton {
      background: #2b2d31;
      border: 1px solid #3a3d44;
      border-radius: 8px;
      padding: 6px 10px;
    }
    QPushButton:hover { background: #32343a; }
    QPushButton:pressed { background: #26282d; }

    QListView {
      background: #1e1f22;
      border: none;
    }
    QListView::item {
      background: #232427;
      border: 1px solid #2f3136;
      border-radius: 10px;
      padding: 4px;
      margin: 2px;
    }
    QListView::item:selected {
      border: 2px solid #5a8dee;
      background: #25272c;
    }
    QScrollBar:vertical {
      background: #1e1f22;
      width: 12px;
      margin: 0px;
    }
    QScrollBar::handle:vertical {
      background: #3a3d44;
      border-radius: 6px;
      min-height: 30px;
    }
    QScrollBar::handle:vertical:hover { background: #4a4e57; }
    QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {
      height: 0px;
    }
    """)

    ensure_dir(DATA_DIR)
    db_path = os.path.join(DATA_DIR, DB_NAME)

    thumbs = os.path.join(DATA_DIR, "thumbs")
    ensure_dir(thumbs)

    db = LibraryDB(db_path)
    w = MainWindow(db, thumbs)
    w.resize(1280, 860)
    w.show()

    sys.exit(app.exec())


if __name__ == "__main__":
    main()