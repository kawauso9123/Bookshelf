# Script Name: Bookshelf.py
# [概要]
# ローカルまたはNAS上の自炊書籍（画像/PDF/ZIP）を管理・閲覧するためのデジタル本棚アプリケーション。
# SQLiteデータベースを使用して高速に検索・フィルタリングを行い、
# 大量の書籍データでもスムーズなブラウジングを実現します。
#
# [主な機能]
# 1. フォルダ階層構造を維持した「棚モード」と、配下すべてを一覧する「フラットモード」の切り替え。
# 2. 書籍（ZIP/PDF/画像フォルダ）のサムネイル自動生成（非同期処理）。
# 3. お気に入り（★）機能によるフィルタリング。
# 4. 外部ビューア（Honeyview）との連携。
# 5. データベースによる高速なメタデータ管理。
#
# [開発・動作環境]
# - Python 3.x / PyQt6
# - Pillow, PyMuPDF (fitz)
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
import random
from collections import deque
from dataclasses import dataclass, field
from typing import Optional, List, Dict, Set, Tuple

from PyQt6.QtCore import (
    Qt, QAbstractListModel, QModelIndex, QSize,
    QObject, pyqtSignal, QRunnable, QThreadPool, QTimer, QSettings, QRect, QPoint, QEvent
)
from PyQt6.QtGui import QIcon, QPixmap, QAction, QPainter, QFont, QShortcut, QKeySequence, QWheelEvent, QMouseEvent, QColor
from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QListView, QPushButton, QLabel, QLineEdit, QComboBox, QMessageBox,
    QFileDialog, QMenu, QAbstractItemView, QDialog, QDialogButtonBox,
    QListWidget, QListWidgetItem, QInputDialog, QCheckBox
)

from PIL import Image, ImageChops
import fitz  # PyMuPDF

# =========================
# USER SETTINGS
# =========================
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
# --- データ保存場所 ---
# スクリプトと同じ場所のdataフォルダに保存する場合:
DATA_DIR = os.path.join(BASE_DIR, "data")
# 固定パスに保存する場合:
#　DATA_DIR = r"P:\log-folder\Bookshelf"

VIEWER_EXE = r""
MEMO_FILE_PATH = r""
# =========================

APP_NAME = "BooK_Shelf"
DB_NAME = "library.sqlite3"

THUMB_SIZE = 320         # サムネ長辺
THUMB_VER = 4            # サムネ方式のバージョン
MAX_THUMB_JOBS = 12      # 同時生成数（NAS負荷を抑える）

IMG_EXTS = {".jpg", ".jpeg", ".png", ".webp", ".gif", ".bmp"}

# ノイズフォルダ除外リスト
NOISE_DIR_NAMES = {
    ".git", ".svn", "__pycache__", ".vs", ".idea",
    "$RECYCLE.BIN", "System Volume Information",
    "tmp", "temp", "_temp", "_trash", "trash",
}

AUTO_TAG_ENABLED_DEFAULT = False
# 混在ビュー（子フォルダカード＋直下の本）用：フォルダカード先頭表示
SHOW_DIRS_FIRST = True
AUTO_LIGHT_SCAN_ON_ENTER_DEFAULT = True
LIGHT_SCAN_RESCAN_SECONDS = 30


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

def extract_auto_tags_from_title(title: str) -> List[str]:
    tags = []

    patterns = [
        r"\(([^()]{1,40})\)",
        r"（([^（）]{1,40})）"
    ]

    for p in patterns:
        for m in re.findall(p, title):
            tag = m.strip()
            if not tag:
                continue
            if tag.isdigit():
                continue
            tags.append(tag)

    # 重複除去
    return list(dict.fromkeys(tags))

def normalize_tag_name(name: str) -> str:
    s = name.strip()
    s = s.replace("　", " ")
    s = re.sub(r"\s+", " ", s)
    return s

def extract_first_bracket_author(text: str) -> Optional[str]:
    """
    行の中で最初に出現する [] を取得し、作者名を返す。

    通常:
        [作者名] -> 作者名

    例外:
        [ABCDE_(あいうえお)] -> あいうえお
        ※ [] 内に最初の () がある場合は、その中身を作者名として優先
    """
    m = re.search(r"\[([^\]]+)\]", text)
    if not m:
        return None

    raw = m.group(1).strip()
    if not raw:
        return None

    # [] 内に (...) がある場合は、その中身を作者名として優先
    m2 = re.search(r"\(([^()]*)\)", raw)
    if m2:
        inner = m2.group(1).strip()
        if inner:
            return inner

    return raw

# -----------------------------
# DB
# -----------------------------
class LibraryDB:
    def __init__(self, db_path: str):
        self.db_path = db_path
        self._lock = threading.RLock()
        self._scan_lock = threading.RLock()
        # timeout を明示（ロック時に即エラーになりにくくする）
        self.conn = sqlite3.connect(self.db_path, check_same_thread=False, timeout=8.0)
        self.conn.row_factory = sqlite3.Row

        # 追加：スキャン専用接続（BEGIN/COMMITを独立させる）
        self.scan_conn = sqlite3.connect(self.db_path, check_same_thread=False, timeout=8.0)
        self.scan_conn.row_factory = sqlite3.Row

        self.sql_count = 0
        self._init()

    def _init(self) -> None:
        with self._lock:
            cur = self.conn.cursor()
            # 追加：DBロック/ビジーの待ち
            cur.execute("PRAGMA busy_timeout=8000;")
            cur.execute("PRAGMA synchronous=NORMAL;")
            cur.execute("PRAGMA foreign_keys=ON;")

            # WALを試し、ダメならDELETEへフォールバック
            try:
                cur.execute("PRAGMA journal_mode=WAL;")
                jm = (cur.fetchone()[0] if cur.description else None)
                if str(jm).upper() != "WAL":
                    cur.execute("PRAGMA journal_mode=DELETE;")
            except sqlite3.OperationalError:
                cur.execute("PRAGMA journal_mode=DELETE;")

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
                hash TEXT,
                cover_state INTEGER NOT NULL DEFAULT 0,  -- 0=none,1=ok,2=fail
                cover_thumb_path TEXT,
                cover_sig TEXT,
                last_scanned_at INTEGER NOT NULL,
                FOREIGN KEY(root_id) REFERENCES roots(id)
            );
            """)

            # Check and add hash column if not exists
            cur.execute("PRAGMA table_info(books)")
            cols = [c["name"] for c in cur.fetchall()]
            if "hash" not in cols:
                cur.execute("ALTER TABLE books ADD COLUMN hash TEXT")

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
                rep_path TEXT,              -- 代表表紙のパス (非★)
                rep_rating INTEGER DEFAULT 0, -- 代表表紙の評価 (非★)
                rep_star_path TEXT,         -- 代表表紙のパス (★)
                rep_star_rating INTEGER DEFAULT 0, -- 代表表紙の評価 (★)
                rep_cached_at INTEGER DEFAULT 0, -- 代表表紙キャッシュ日時
                rep_sig TEXT,               -- 代表表紙キャッシュのシグネチャ (配下の変化検出用)
                PRIMARY KEY(root_id, rel_dir)
            );
            """)
            cur.execute("CREATE INDEX IF NOT EXISTS idx_dirs_parent ON dirs(root_id, parent_dir);")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_dirs_name ON dirs(root_id, name);")

            # booksの補助インデックス（代表選択高速化）
            cur.execute("CREATE INDEX IF NOT EXISTS idx_books_rel_path ON books(root_id, rel_path);")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_books_root_rel_mtime ON books(root_id, rel_path, mtime);")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_books_root_type_rel ON books(root_id, type, rel_path);")

            cur.execute("CREATE INDEX IF NOT EXISTS idx_books_root ON books(root_id);")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_books_parent_dir ON books(parent_dir);")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_books_title ON books(title);")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_meta_rating ON meta(rating);")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_books_root_parent ON books(root_id, parent_dir);")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_meta_path_rating ON meta(path, rating);")

            cur.execute("""
            CREATE TABLE IF NOT EXISTS dir_meta(
                root_id INTEGER NOT NULL,
                rel_dir TEXT NOT NULL,
                rating INTEGER NOT NULL DEFAULT 0,
                PRIMARY KEY(root_id, rel_dir),
                FOREIGN KEY(root_id) REFERENCES roots(id)
            );
            """)
            cur.execute("CREATE INDEX IF NOT EXISTS idx_dir_meta_rating ON dir_meta(rating);")

            cur.execute("""
            CREATE TABLE IF NOT EXISTS reading(
                path TEXT PRIMARY KEY,
                last_opened_at INTEGER,
                open_count INTEGER DEFAULT 0
            );
            """)

            # Tagging System
            cur.execute("""
            CREATE TABLE IF NOT EXISTS tags(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT UNIQUE NOT NULL,
                created_at INTEGER NOT NULL,
                color TEXT DEFAULT NULL,
                sort_order INTEGER DEFAULT 0
            );
            """)
            cur.execute("""
            CREATE TABLE IF NOT EXISTS book_tags(
                path TEXT NOT NULL,
                tag_id INTEGER NOT NULL,
                source TEXT NOT NULL DEFAULT 'manual',  -- 'auto' / 'manual' / 'memo'
                created_at INTEGER NOT NULL,
                PRIMARY KEY(path, tag_id),
                FOREIGN KEY(path) REFERENCES books(path),
                FOREIGN KEY(tag_id) REFERENCES tags(id)
            );
            """)
            cur.execute("CREATE INDEX IF NOT EXISTS idx_book_tags_path ON book_tags(path);")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_book_tags_tag_id ON book_tags(tag_id);")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_tags_name ON tags(name);")

            # scan_conn にも同じPRAGMA（同じ方針で動かす）
            cur2 = self.scan_conn.cursor()
            cur2.execute("PRAGMA busy_timeout=8000;")
            cur2.execute("PRAGMA synchronous=NORMAL;")
            cur2.execute("PRAGMA foreign_keys=ON;")
            try:
                cur2.execute("PRAGMA journal_mode=WAL;")
                jm2 = (cur2.fetchone()[0] if cur2.description else None)
                if str(jm2).upper() != "WAL":
                    cur2.execute("PRAGMA journal_mode=DELETE;")
            except sqlite3.OperationalError:
                cur2.execute("PRAGMA journal_mode=DELETE;")
            self.scan_conn.commit()

            self.conn.commit()

    def _exec_write(self, sql: str, params: tuple = (), *, retries: int = 10) -> None:
        """
        NAS/多重起動で一瞬だけロックしたときに、短い待ち＋リトライで吸収する。
        """
        with self._lock:
            last = None
            for i in range(retries):
                try:
                    cur = self.conn.cursor()
                    cur.execute(sql, params)
                    self.conn.commit()
                    return
                except sqlite3.OperationalError as e:
                    msg = str(e).lower()
                    if ("locked" in msg) or ("busy" in msg):
                        # 少しずつ待ち時間を伸ばす（ジッタ入り）
                        time.sleep((0.06 * (i + 1)) + random.uniform(0.0, 0.04))
                        last = e
                        continue
                    raise
            raise last if last else sqlite3.OperationalError("DB write failed")

    def upsert_root(self, root_path: str) -> int:
        root_path = norm(root_path)
        now = int(time.time())

        # 書き込みは _exec_write がロックとcommitを持つ
        self._exec_write("""
        INSERT INTO roots(path, created_at) VALUES(?, ?)
        ON CONFLICT(path) DO UPDATE SET created_at=excluded.created_at
        """, (root_path, now))

        # id取得は読み取りなのでロック
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("SELECT id FROM roots WHERE path=?", (root_path,))
            row = cur.fetchone()
            root_id = int(row["id"])

        # dirsのルート行確保（書き込み）
        self._exec_write("""
        INSERT OR IGNORE INTO dirs(root_id, rel_dir, parent_dir, name, mtime, last_scanned_at)
        VALUES(?, ?, ?, ?, ?, ?)
        """, (root_id, "", "", "", now, now))

        return root_id

    def get_roots(self) -> List[str]:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("SELECT path FROM roots ORDER BY created_at DESC")
            return [r["path"] for r in cur.fetchall()]

    def upsert_book(self, *, path: str, root_id: int, rel_path: str, parent_dir: str,
                    btype: str, size: int, mtime: int, title: str, autocommit: bool = True,
                    conn: Optional[sqlite3.Connection] = None, hash_val: Optional[str] = None) -> None:
        conn = conn or self.conn
        lock = self._scan_lock if conn == self.scan_conn else self._lock
        with lock:
            now = int(time.time())
            cur = conn.cursor()
            cur.execute("""
            INSERT INTO books(path, root_id, rel_path, parent_dir, type, size, mtime, title, last_scanned_at, hash)
            VALUES(?,?,?,?,?,?,?,?,?,?)
            ON CONFLICT(path) DO UPDATE SET
                root_id=excluded.root_id,
                rel_path=excluded.rel_path,
                parent_dir=excluded.parent_dir,
                type=excluded.type,
                size=excluded.size,
                mtime=excluded.mtime,
                title=excluded.title,
                last_scanned_at=excluded.last_scanned_at,
                hash=CASE WHEN excluded.hash IS NOT NULL THEN excluded.hash WHEN books.size != excluded.size OR books.mtime != excluded.mtime THEN NULL ELSE books.hash END
            """, (path, root_id, rel_path, parent_dir, btype, size, mtime, title, now, hash_val))
            if autocommit:
                conn.commit()

    def get_dir_row(self, root_id: int, rel_dir: str) -> Optional[sqlite3.Row]:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute(
                "SELECT root_id, rel_dir, parent_dir, name, mtime, last_scanned_at FROM dirs WHERE root_id=? AND rel_dir=?",
                (int(root_id), rel_dir or "")
            )
            return cur.fetchone()

    def get_book_brief(self, path: str) -> Optional[sqlite3.Row]:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute(
                "SELECT path, size, mtime, parent_dir, rel_path, title, type FROM books WHERE path=?",
                (path,)
            )
            return cur.fetchone()

    def set_rating(self, path: str, rating: int) -> None:
        self._exec_write("""
            INSERT INTO meta(path, rating) VALUES(?,?)
            ON CONFLICT(path) DO UPDATE SET rating=excluded.rating
            """, (path, int(rating)))

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

    def upsert_dir(self, *, root_id: int, rel_dir: str, parent_dir: str, name: str, mtime: int, autocommit: bool = True,
                   conn: Optional[sqlite3.Connection] = None) -> None:
        conn = conn or self.conn
        lock = self._scan_lock if conn == self.scan_conn else self._lock
        with lock:
            now = int(time.time())
            cur = conn.cursor()
            cur.execute("""
            INSERT INTO dirs(root_id, rel_dir, parent_dir, name, mtime, last_scanned_at)
            VALUES(?,?,?,?,?,?)
            ON CONFLICT(root_id, rel_dir) DO UPDATE SET
                parent_dir=excluded.parent_dir,
                name=excluded.name,
                mtime=excluded.mtime,
                last_scanned_at=excluded.last_scanned_at
            """, (root_id, rel_dir, parent_dir, name, int(mtime), now))
            if autocommit:
                conn.commit()

    def list_child_dirs(self, root_id: int, parent_dir: str, query: str = "", min_rating: int = 0, tag_filter: str = "") -> List[sqlite3.Row]:
        with self._lock:
            self.sql_count += 1
            q_param = f"%{query.strip()}%" if query.strip() else "%"
            cur = self.conn.cursor()

            # ★のみ・検索なし・タグなし専用
            if min_rating >= 1 and not query.strip() and not tag_filter:
                prefix = (parent_dir + "\\") if parent_dir else ""
                prefix_len = len(prefix)

                cur.execute(f"""
                WITH starred AS (
                    SELECT
                        CASE
                            WHEN instr(substr(b.rel_path, {prefix_len + 1}), '\\') > 0
                                THEN substr(
                                    substr(b.rel_path, {prefix_len + 1}),
                                    1,
                                    instr(substr(b.rel_path, {prefix_len + 1}), '\\') - 1
                                )
                            ELSE '.'
                        END AS child
                    FROM books b
                    JOIN meta m ON m.path = b.path
                    WHERE b.root_id = ?
                      AND b.type IN ('zip','pdf')
                      AND b.rel_path LIKE ?
                      AND COALESCE(m.rating,0) >= 1
                ),
                starred_child AS (
                    SELECT DISTINCT child
                    FROM starred
                    WHERE child <> '.'
                )
                SELECT d.rel_dir, d.name, d.mtime, COALESCE(dm.rating, 0) AS rating
                FROM dirs d
                LEFT JOIN dir_meta dm
                  ON dm.root_id = d.root_id AND dm.rel_dir = d.rel_dir
                WHERE d.root_id = ?
                  AND d.parent_dir = ?
                  AND (
                        COALESCE(dm.rating, 0) >= 1
                        OR d.name IN (SELECT child FROM starred_child)
                  )
                ORDER BY d.name
                """, (root_id, prefix + "%", root_id, parent_dir))
                return cur.fetchall()

            sql = "SELECT d.rel_dir, d.name, d.mtime, COALESCE(dm.rating, 0) as rating FROM dirs d LEFT JOIN dir_meta dm ON dm.root_id=d.root_id AND dm.rel_dir=d.rel_dir"
            sql += " WHERE d.root_id=? AND d.parent_dir=?"
            params = [root_id, parent_dir]

            # 1. Tag Filter (Must contain tagged book)
            if tag_filter:
                sql += """
                AND EXISTS (
                    SELECT 1 FROM books b
                    JOIN book_tags bt ON bt.path=b.path
                    JOIN tags t ON t.id=bt.tag_id
                    WHERE b.root_id=d.root_id AND b.rel_path LIKE d.rel_dir || '\\%'
                    AND t.name = ?
                )
                """
                params.append(tag_filter)

            # 2. Min Rating
            if min_rating > -1:
                sql += """
                AND (COALESCE(dm.rating, 0) >= ? OR EXISTS(
                    SELECT 1 FROM books b LEFT JOIN meta m ON m.path=b.path
                    WHERE b.root_id=d.root_id AND b.rel_path LIKE d.rel_dir || '\\%' AND COALESCE(m.rating,0) >= ?
                ))
                """
                params.extend([min_rating, min_rating])

            # 3. Query
            if query.strip():
                sql += """
                AND (
                    d.name LIKE ?
                    OR EXISTS (
                        SELECT 1 FROM books b
                        WHERE b.root_id=d.root_id AND b.rel_path LIKE d.rel_dir || '\\%'
                        AND (b.title LIKE ? OR b.rel_path LIKE ?)
                    )
                )
                """
                params.extend([q_param, q_param, q_param])

            sql += " ORDER BY d.name"
            cur.execute(sql, tuple(params))
            return cur.fetchall()

    def list_direct_books(self, root_id: int, dir_rel: str, query: str = "", min_rating: int = 0, tag_filter: str = "") -> List[sqlite3.Row]:
        """dir_rel直下の本だけ（混在ビュー用）"""
        with self._lock:
            self.sql_count += 1
            q = f"%{query.strip()}%" if query.strip() else "%"
            cur = self.conn.cursor()
            
            sql = """
            SELECT b.*, COALESCE(m.rating,0) AS rating
            FROM books b
            LEFT JOIN meta m ON m.path=b.path
            """
            params = []
            
            if tag_filter:
                sql += " JOIN book_tags bt ON bt.path=b.path JOIN tags t ON t.id=bt.tag_id "
            
            sql += " WHERE b.root_id=? AND b.parent_dir=? "
            params.extend([root_id, dir_rel])
            
            if tag_filter:
                sql += " AND t.name=? "
                params.append(tag_filter)
            
            sql += " AND COALESCE(m.rating,0) >= ? AND (b.title LIKE ? OR b.rel_path LIKE ?) ORDER BY b.title "
            params.extend([min_rating, q, q])
            
            cur.execute(sql, tuple(params))
            return cur.fetchall()

    def get_dir_rep_path(self, root_id: int, dir_rel: str, only_star: bool = False) -> Optional[Tuple[str, int, int, int]]:
        """フォルダカードの代表表紙：☆優先→mtime新しい（配下全部から1つ）"""
        with self._lock:
            self.sql_count += 1
            cur = self.conn.cursor()
            like = (dir_rel + r"\%") if dir_rel else "%"
            if only_star:
                cur.execute("""
                SELECT b.path, COALESCE(m.rating,0) as rating
                , b.mtime, b.size FROM books b
                LEFT JOIN meta m ON m.path=b.path
                WHERE b.root_id=? AND b.rel_path LIKE ?
                  AND b.type IN ('zip','pdf')
                  AND COALESCE(m.rating,0) > 0
                ORDER BY COALESCE(m.rating,0) DESC, b.mtime DESC
                LIMIT 1
                """, (root_id, like))
            else:
                cur.execute("""
                SELECT b.path, COALESCE(m.rating,0) as rating
                , b.mtime, b.size FROM books b
                LEFT JOIN meta m ON m.path=b.path
                WHERE b.root_id=? AND b.rel_path LIKE ?
                  AND b.type IN ('zip','pdf')
                ORDER BY COALESCE(m.rating,0) DESC, b.mtime DESC
                LIMIT 1
                """, (root_id, like))
            row = cur.fetchone() # type: ignore
            return (row["path"], int(row["rating"]), int(row["mtime"]), int(row["size"])) if row else None

    def list_books(self, root_id: int, query: str = "", min_rating: int = 0, dir_rel: str = "", tag_filter: str = "") -> List[sqlite3.Row]:
        with self._lock:
            self.sql_count += 1
            q = f"%{query.strip()}%" if query.strip() else "%"
            cur = self.conn.cursor()

            where_dir = ""
            params: list = [root_id]

            if dir_rel:
                # dir_rel配下のみ（rel_pathは \ 区切り想定）
                where_dir = " AND b.rel_path LIKE ? "
                params.append(dir_rel + r"\%")

            sql = f"""
            SELECT b.*, COALESCE(m.rating,0) AS rating
            FROM books b
            LEFT JOIN meta m ON m.path=b.path
            """
            
            if tag_filter:
                sql += " JOIN book_tags bt ON bt.path=b.path JOIN tags t ON t.id=bt.tag_id "
            
            sql += f" WHERE b.root_id=? {where_dir} "
            
            if tag_filter:
                sql += " AND t.name=? "
                params.append(tag_filter)
            
            sql += " AND COALESCE(m.rating,0) >= ? AND (b.title LIKE ? OR b.rel_path LIKE ?) ORDER BY b.parent_dir, b.title "
            params += [min_rating, q, q]

            cur.execute(sql, tuple(params))
            return cur.fetchall()

    def list_books_recursive(self, root_id: int, dir_rel: str, query: str = "", min_rating: int = 0, tag_filter: str = "") -> List[sqlite3.Row]:
        with self._lock:
            self.sql_count += 1
            q = f"%{query.strip()}%" if query.strip() else "%"
            like = (dir_rel + r"\%") if dir_rel else "%"
            cur = self.conn.cursor()

            sql = """
            SELECT b.*, COALESCE(m.rating,0) AS rating
            FROM books b
            LEFT JOIN meta m ON m.path=b.path
            """
            params = [root_id, like]
            
            if tag_filter:
                sql += " JOIN book_tags bt ON bt.path=b.path JOIN tags t ON t.id=bt.tag_id "
            
            sql += " WHERE b.root_id=? AND b.rel_path LIKE ? "
            
            if tag_filter:
                sql += " AND t.name=? "
                params.append(tag_filter)
            
            sql += " AND COALESCE(m.rating,0) >= ? AND (b.title LIKE ? OR b.rel_path LIKE ?) ORDER BY b.parent_dir, b.title "
            params.extend([min_rating, q, q])
            
            cur.execute(sql, tuple(params))
            return cur.fetchall()

    def list_folder_buckets(self, root_id: int, query: str = "", min_rating: int = 0, dir_rel: str = "", tag_filter: str = "") -> List[dict]:
        with self._lock:
            rows = self.list_books(root_id, query=query, min_rating=min_rating, dir_rel=dir_rel, tag_filter=tag_filter)
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

    def get_book_rel_path(self, path: str) -> Optional[str]:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("SELECT rel_path FROM books WHERE path=?", (path,))
            row = cur.fetchone()
            return str(row["rel_path"]) if row else None

    def list_child_dir_reps(self, root_id: int, parent_dir: str, query: str = "", only_star: bool = False) -> Dict[str, Tuple[str, int]]:
        """
        parent_dir 直下の「子フォルダごとの代表表紙」を1回のSQLで取得する。
        戻り値: { child_name: (rep_path, rating) }  ※ child_name は dirs.name と一致
        """
        with self._lock:
            self.sql_count += 1
            q = f"%{query.strip()}%" if query.strip() else "%"
            cur = self.conn.cursor()

            # prefix: parent_dir\  （root直下は ""）
            prefix = (parent_dir + "\\") if parent_dir else ""
            prefix_len = len(prefix)

            # rel_path の prefix 以降から最初の "\" までを child として切り出す
            # 例: parent="A" → rel_path="A\B\c.zip" → rest="B\c.zip" → child="B"
            #     parent="A" → rel_path="A\x.zip"   → rest="x.zip"   → child="."（直下本）
            # ここでは child="." は除外（直下本は別表示のため）
            base_sql = f"""
            WITH cand AS (
              SELECT
                b.path AS path,
                COALESCE(m.rating, 0) AS rating,
                b.mtime AS mtime,
                b.title AS title,
                CASE
                  WHEN instr(substr(b.rel_path, {prefix_len + 1}), '\\') > 0
                    THEN substr(substr(b.rel_path, {prefix_len + 1}), 1, instr(substr(b.rel_path, {prefix_len + 1}), '\\') - 1)
                  ELSE '.'
                END AS child
              FROM books b
              LEFT JOIN meta m ON m.path = b.path
              WHERE b.root_id = ?
                AND b.rel_path LIKE ?
                AND b.type IN ('zip','pdf')
                AND (b.title LIKE ? OR b.rel_path LIKE ?)
                {"AND COALESCE(m.rating,0) > 0" if only_star else ""}
            ),
            ranked AS (
              SELECT *,
                     ROW_NUMBER() OVER (PARTITION BY child ORDER BY rating DESC, mtime DESC, title DESC) AS rn
              FROM cand
              WHERE child <> '.'
            )
            SELECT child, path, rating
            FROM ranked
            WHERE rn = 1
            """

            cur.execute(base_sql, (root_id, prefix + "%", q, q))
            out: Dict[str, Tuple[str, int]] = {}
            for r in cur.fetchall():
                out[str(r["child"])] = (str(r["path"]), int(r["rating"]))
            return out

    def list_recent_books(self, root_id: int, limit: int = 200) -> List[sqlite3.Row]:
        with self._lock:
            self.sql_count += 1
            cur = self.conn.cursor()

            cutoff = int(time.time()) - 30 * 86400

            cur.execute("""
            SELECT b.*, COALESCE(m.rating,0) AS rating
            FROM books b
            LEFT JOIN meta m ON m.path=b.path
            WHERE b.root_id=?
            AND COALESCE(m.rating,0) >= 0
            AND b.mtime >= ?
            ORDER BY b.mtime DESC
            LIMIT ?
            """, (root_id, cutoff, limit))
            return cur.fetchall()

    def list_unread_books(self, root_id: int) -> List[sqlite3.Row]:
        with self._lock:
            self.sql_count += 1
            cur = self.conn.cursor()
            cur.execute("""
            SELECT b.*, COALESCE(m.rating,0) AS rating
            FROM books b
            LEFT JOIN reading r ON r.path=b.path
            LEFT JOIN meta m ON m.path=b.path
            WHERE b.root_id=? AND r.path IS NULL
            AND COALESCE(m.rating,0) >= 0
            ORDER BY b.mtime DESC
            """, (root_id,))
            return cur.fetchall()

    def list_duplicate_books(self, root_id: int) -> List[sqlite3.Row]:
        """ハッシュ重複のある本をすべて取得"""
        with self._lock:
            self.sql_count += 1
            cur = self.conn.cursor()
            cur.execute("""
            SELECT b.*, COALESCE(m.rating,0) AS rating
            FROM books b
            LEFT JOIN meta m ON m.path=b.path
            WHERE b.root_id=? AND b.hash IN (SELECT hash FROM books WHERE root_id=? AND hash IS NOT NULL GROUP BY hash HAVING COUNT(*) > 1)
            ORDER BY b.hash, b.path
            """, (root_id, root_id))
            return cur.fetchall()

    def ensure_tag(self, name: str, conn: Optional[sqlite3.Connection] = None, autocommit: bool = True) -> int:
        name = name.strip()
        conn = conn or self.conn
        lock = self._scan_lock if conn == self.scan_conn else self._lock
        with lock:
            cur = conn.cursor()
            cur.execute("SELECT id FROM tags WHERE name=?", (name,))
            row = cur.fetchone()
            if row:
                return int(row["id"])
            
            now = int(time.time())
            cur.execute("INSERT INTO tags(name, created_at) VALUES(?, ?)", (name, now))
            if autocommit:
                conn.commit()
            
            cur.execute("SELECT id FROM tags WHERE name=?", (name,))
            row = cur.fetchone()
            return int(row["id"])

    def get_tag_id(self, name: str) -> Optional[int]:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("SELECT id FROM tags WHERE name=?", (name,))
            row = cur.fetchone()
            return int(row["id"]) if row else None

    def get_all_tags(self) -> List[sqlite3.Row]:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("SELECT * FROM tags ORDER BY sort_order, name")
            return cur.fetchall()

    def get_all_tags_with_count(self) -> List[sqlite3.Row]:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("""
                SELECT t.id, t.name, t.color, t.sort_order, COUNT(bt.path) AS book_count
                FROM tags t
                LEFT JOIN book_tags bt ON bt.tag_id = t.id
                GROUP BY t.id, t.name, t.color, t.sort_order
                ORDER BY t.sort_order, t.name
            """)
            return cur.fetchall()

    def rename_tag(self, tag_id: int, new_name: str) -> None:
        new_name = new_name.strip()
        if not new_name: return
        self._exec_write("UPDATE tags SET name=? WHERE id=?", (new_name, tag_id))

    def delete_tag(self, tag_id: int) -> None:
        with self._lock:
            self._exec_write("DELETE FROM book_tags WHERE tag_id=?", (tag_id,))
            self._exec_write("DELETE FROM tags WHERE id=?", (tag_id,))

    def merge_tags(self, src_tag_id: int, dst_tag_id: int) -> None:
        if src_tag_id == dst_tag_id:
            return

        with self._lock:
            cur = self.conn.cursor()
            try:
                cur.execute("BEGIN;")

                # すでに同じ path に dst がある場合は、src 側を消す
                cur.execute("""
                    DELETE FROM book_tags
                    WHERE tag_id = ?
                      AND path IN (
                          SELECT path FROM book_tags WHERE tag_id = ?
                      )
                """, (src_tag_id, dst_tag_id))

                # 残りを dst へ寄せる
                cur.execute("""
                    UPDATE book_tags
                    SET tag_id = ?
                    WHERE tag_id = ?
                """, (dst_tag_id, src_tag_id))

                # src タグ本体を削除
                cur.execute("DELETE FROM tags WHERE id = ?", (src_tag_id,))

                self.conn.commit()
            except Exception:
                self.conn.rollback()
                raise

    def add_tag_to_book(self, path: str, tag_name: str, source: str = "manual") -> None:
        tag_id = self.ensure_tag(tag_name)
        now = int(time.time())
        self._exec_write("""
            INSERT OR IGNORE INTO book_tags(path, tag_id, source, created_at)
            VALUES(?, ?, ?, ?)
        """, (path, tag_id, source, now))

    def remove_tag_from_book(self, path: str, tag_name: str) -> None:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("SELECT id FROM tags WHERE name=?", (tag_name,))
            row = cur.fetchone()
            if not row:
                return
            tag_id = int(row["id"])
            self._exec_write("DELETE FROM book_tags WHERE path=? AND tag_id=?", (path, tag_id))

    def set_book_tags(self, path: str, tag_names: List[str], source: str = "manual", conn: Optional[sqlite3.Connection] = None, autocommit: bool = True) -> None:
        conn = conn or self.conn
        lock = self._scan_lock if conn == self.scan_conn else self._lock
        with lock:
            tag_ids = []
            for name in tag_names:
                tag_ids.append(self.ensure_tag(name, conn=conn, autocommit=autocommit))
            
            now = int(time.time())
            cur = conn.cursor()
            cur.execute("DELETE FROM book_tags WHERE path=? AND source=?", (path, source))
            
            for tid in tag_ids:
                if source == "manual":
                    cur.execute("""
                        INSERT INTO book_tags(path, tag_id, source, created_at)
                        VALUES(?, ?, ?, ?)
                        ON CONFLICT(path, tag_id) DO UPDATE SET source=excluded.source, created_at=excluded.created_at
                    """, (path, tid, source, now))
                else:
                    cur.execute("""
                        INSERT OR IGNORE INTO book_tags(path, tag_id, source, created_at)
                        VALUES(?, ?, ?, ?)
                    """, (path, tid, source, now))
            if autocommit:
                conn.commit()

    def replace_auto_tags_for_book(self, path: str, auto_tag_names: List[str], conn: Optional[sqlite3.Connection] = None, autocommit: bool = True) -> None:
        self.set_book_tags(path, auto_tag_names, source="auto", conn=conn, autocommit=autocommit)

    def get_tags_for_book(self, path: str) -> List[sqlite3.Row]:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("""
                SELECT t.id, t.name, t.color, bt.source
                FROM book_tags bt
                JOIN tags t ON bt.tag_id = t.id
                WHERE bt.path = ?
                ORDER BY t.sort_order, t.name
            """, (path,))
            return cur.fetchall()

    def import_memo_tags(self, filenames: List[str], tag_name: str = "#_memo") -> int:
        with self._lock:
            tag_id = self.ensure_tag(tag_name)
            
            cur = self.conn.cursor()
            cur.execute("SELECT path, rel_path FROM books")
            rows = cur.fetchall()
            name_map = {os.path.basename(r["rel_path"]): r["path"] for r in rows}
            
            target_paths = []
            for fn in filenames:
                if fn in name_map:
                    target_paths.append(name_map[fn])
            
            if not target_paths:
                return 0

            now = int(time.time())
            try:
                cur.execute("BEGIN;")
                cur.execute("DELETE FROM book_tags WHERE tag_id=? AND source='memo'", (tag_id,))
                data = [(path, tag_id, 'memo', now) for path in target_paths]
                cur.executemany("""
                    INSERT OR IGNORE INTO book_tags(path, tag_id, source, created_at)
                    VALUES(?, ?, ?, ?)
                """, data)
                self.conn.commit()
                return len(target_paths)
            except Exception:
                self.conn.rollback()
                return 0

    def list_books_by_tag(self, root_id: int, tag_names: List[str], dir_rel: str = "", min_rating: int = 0) -> List[sqlite3.Row]:
        if not tag_names:
            return []

        with self._lock:
            self.sql_count += 1
            cur = self.conn.cursor()
            
            placeholders = ",".join(["?"] * len(tag_names))
            
            where_dir = ""
            params = [root_id]
            if dir_rel:
                where_dir = " AND b.rel_path LIKE ? "
                params.append(dir_rel + r"\%")
            
            params.extend(tag_names)
            params.append(min_rating)
            params.append(len(set(tag_names)))
            
            sql = f"""
            SELECT b.*, COALESCE(m.rating,0) AS rating
            FROM books b
            LEFT JOIN meta m ON m.path=b.path
            JOIN book_tags bt ON b.path = bt.path
            JOIN tags t ON bt.tag_id = t.id
            WHERE b.root_id=? {where_dir}
              AND t.name IN ({placeholders})
              AND COALESCE(m.rating,0) >= ?
            GROUP BY b.path
            HAVING COUNT(DISTINCT t.id) = ?
            ORDER BY b.parent_dir, b.title
            """
            
            cur.execute(sql, tuple(params))
            return cur.fetchall()

    def get_tags_bulk_for_paths(self, paths: List[str]) -> Dict[str, List[str]]:
        if not paths:
            return {}
        with self._lock:
            cur = self.conn.cursor()
            placeholders = ",".join(["?"] * len(paths))
            sql = f"""
            SELECT bt.path, t.name
            FROM book_tags bt
            JOIN tags t ON bt.tag_id = t.id
            WHERE bt.path IN ({placeholders})
            ORDER BY t.sort_order, t.name
            """
            cur.execute(sql, tuple(paths))
            
            res = {}
            for row in cur.fetchall():
                p = row["path"]
                t = row["name"]
                if p not in res:
                    res[p] = []
                res[p].append(t)
            return res

    # --- Manual Tag CRUD (Aliases/Wrappers for compatibility) ---
    def create_tag(self, name: str) -> int:
        name = name.strip()
        if not name: return -1
        return self.ensure_tag(name)

    def list_tags(self) -> List[sqlite3.Row]:
        return self.get_all_tags()

    def set_book_tag(self, path: str, tag_name: str, source: str = "manual") -> None:
        self.add_tag_to_book(path, tag_name, source)

    def remove_book_tag(self, path: str, tag_name: str) -> None:
        self.remove_tag_from_book(path, tag_name)

    def get_book_tags(self, path: str) -> List[str]:
        return [r["name"] for r in self.get_tags_for_book(path)]

    def mark_opened(self, path: str) -> None:
        now = int(time.time())
        self._exec_write("""
        INSERT INTO reading(path,last_opened_at,open_count)
        VALUES(?,?,1)
        ON CONFLICT(path) DO UPDATE SET
            last_opened_at=?,
            open_count=open_count+1
        """, (path, now, now))

    def get_ratings_bulk(self, paths: List[str]) -> Dict[str, int]:
        """meta を IN で一括取得"""
        if not paths:
            return {}
        with self._lock:
            cur = self.conn.cursor()
            placeholders = ",".join(["?"] * len(paths))
            cur.execute(f"SELECT path, rating FROM meta WHERE path IN ({placeholders})", tuple(paths))
            return {str(r["path"]): int(r["rating"]) for r in cur.fetchall()}

    def set_dir_rating(self, root_id: int, rel_dir: str, rating: int) -> None:
        self._exec_write("""
        INSERT INTO dir_meta(root_id, rel_dir, rating) VALUES(?,?,?)
        ON CONFLICT(root_id, rel_dir) DO UPDATE SET rating=excluded.rating
        """, (int(root_id), rel_dir or "", int(rating)))

    def star_root_author_dirs(self, root_id: int, authors: Set[str]) -> int:
        """
        Root直下の作者フォルダ(name=作者名, parent_dir='')に★を付ける。
        戻り値: 実際に★を付けたフォルダ数
        """
        if not authors:
            return 0

        with self._lock:
            cur = self.conn.cursor()

            placeholders = ",".join(["?"] * len(authors))
            params = [int(root_id), ""] + sorted(authors)

            cur.execute(
                f"""
                SELECT rel_dir, name
                FROM dirs
                WHERE root_id=? AND parent_dir=? AND name IN ({placeholders})
                """,
                tuple(params)
            )
            rows = cur.fetchall()

            count = 0
            for r in rows:
                rel_dir = r["rel_dir"]
                cur.execute(
                    """
                    INSERT INTO dir_meta(root_id, rel_dir, rating)
                    VALUES(?, ?, 1)
                    ON CONFLICT(root_id, rel_dir) DO UPDATE SET rating=1
                    """,
                    (int(root_id), rel_dir)
                )
                count += 1

            self.conn.commit()
            return count

    def get_dir_rating(self, root_id: int, rel_dir: str) -> int:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("SELECT rating FROM dir_meta WHERE root_id=? AND rel_dir=?", (int(root_id), rel_dir or ""))
            row = cur.fetchone()
            return int(row["rating"]) if row else 0

    def get_dir_ratings_bulk(self, root_id: int, rel_dirs: List[str]) -> Dict[str, int]:
        if not rel_dirs:
            return {}
        with self._lock:
            cur = self.conn.cursor()
            placeholders = ",".join(["?"] * len(rel_dirs))
            params = [int(root_id)] + [(d or "") for d in rel_dirs]
            cur.execute(f"SELECT rel_dir, rating FROM dir_meta WHERE root_id=? AND rel_dir IN ({placeholders})", tuple(params))
            return {str(r["rel_dir"]): int(r["rating"]) for r in cur.fetchall()}

    def set_thumb_ok(self, path: str, thumb_path: str, cover_sig: str) -> None:
        self._exec_write("""
            UPDATE books SET cover_state=1, cover_thumb_path=?, cover_sig=?
            WHERE path=?
            """, (thumb_path, cover_sig, path))

    def set_thumb_fail(self, path: str, cover_sig: str) -> None:
        self._exec_write("""
            UPDATE books SET cover_state=2, cover_sig=?
            WHERE path=?
            """, (cover_sig, path))

    def get_child_dir_rep_cache(self, root_id: int, parent_dir: str, only_star: bool = False) -> Dict[str, Tuple[str, int]]:
        """
        Retrieves cached representative cover paths and ratings for child directories.
        Prioritizes starred rep if `only_star` is True, with fallback to non-starred if no starred rep.
        Returns: { child_name: (rep_path, rating) }
        Only returns valid (non-stale) cache entries.
        """
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("""
                SELECT
                    d.rel_dir,
                    d.name,
                    d.last_scanned_at,
                    d.rep_path,
                    d.rep_rating,
                    d.rep_star_path,
                    d.rep_star_rating,
                    d.rep_sig
                FROM dirs d
                WHERE d.root_id=? AND d.parent_dir=?
            """, (root_id, parent_dir))

            results: Dict[str, Tuple[str, int]] = {}
            for row in cur.fetchall():
                rel_dir = row["rel_dir"]
                name = row["name"]
                last_scanned_at = row["last_scanned_at"]
                cached_rep_sig = row["rep_sig"]

                current_rep_sig = sha1(f"{rel_dir}|{last_scanned_at}")

                if not cached_rep_sig or cached_rep_sig != current_rep_sig:
                    continue

                rep_path = None
                rep_rating = 0

                if only_star:
                    if row["rep_star_path"]:
                        rep_path, rep_rating = row["rep_star_path"], row["rep_star_rating"]
                    elif row["rep_path"]: # Fallback to non-starred if no starred rep
                        rep_path, rep_rating = row["rep_path"], row["rep_rating"]
                else:
                    if row["rep_path"]:
                        rep_path, rep_rating = row["rep_path"], row["rep_rating"]
                    elif row["rep_star_path"]: # Fallback to starred if no non-starred rep
                        rep_path, rep_rating = row["rep_star_path"], row["rep_star_rating"]

                if rep_path:
                    results[name] = (rep_path, int(rep_rating))
            return results

    def update_dir_rep_cache(self, root_id: int, rel_dir: str) -> None:
        """
        Calculates and updates the representative cover cache for a single directory.
        """
        with self._lock:
            cur = self.conn.cursor()

            # Get the directory's last_scanned_at for rep_sig
            cur.execute("SELECT last_scanned_at FROM dirs WHERE root_id=? AND rel_dir=?", (root_id, rel_dir))
            dir_info = cur.fetchone()
            if not dir_info:
                # Directory not found, cannot update cache
                return

            dir_last_scanned_at = dir_info["last_scanned_at"]

            # Get non-starred representative book
            rep_path, rep_rating, rep_mtime, rep_size = self.get_dir_rep_path(root_id, rel_dir, only_star=False) or (None, 0, 0, 0)

            # Get starred representative book
            rep_star_path, rep_star_rating, rep_star_mtime, rep_star_size = self.get_dir_rep_path(root_id, rel_dir, only_star=True) or (None, 0, 0, 0)
            
            rep_cached_at = int(time.time())
            # rep_sig: Hash of the directory's relative path and its last_scanned_at.
            # This ensures the cache is invalidated if the directory itself or its contents
            # (which would update last_scanned_at during a scan) change.
            rep_sig = sha1(f"{rel_dir}|{dir_last_scanned_at}")

            self._exec_write("""
                UPDATE dirs SET
                    rep_path=?,
                    rep_rating=?,
                    rep_star_path=?,
                    rep_star_rating=?,
                    rep_cached_at=?,
                    rep_sig=?
                WHERE root_id=? AND rel_dir=?
            """, (
                rep_path, rep_rating,
                rep_star_path, rep_star_rating,
                rep_cached_at, rep_sig,
                root_id, rel_dir
            ))

    def update_single_dir_rep_cache(self, root_id: int, rel_dir: str) -> None:
        rep = self.get_dir_rep_path(root_id, rel_dir, only_star=False)
        rep_star = self.get_dir_rep_path(root_id, rel_dir, only_star=True)

        with self._lock:
            cur = self.conn.cursor()
            cur.execute("SELECT last_scanned_at FROM dirs WHERE root_id=? AND rel_dir=?", (root_id, rel_dir))
            row = cur.fetchone()
            if not row:
                return
            rep_sig = sha1(f"{rel_dir}|{row['last_scanned_at']}")

        self._exec_write("""
            UPDATE dirs
            SET rep_path=?, rep_rating=?, rep_star_path=?, rep_star_rating=?, rep_cached_at=?, rep_sig=?
            WHERE root_id=? AND rel_dir=?
        """, (
            rep[0] if rep else None,
            int(rep[1]) if rep else 0,
            rep_star[0] if rep_star else None,
            int(rep_star[1]) if rep_star else 0,
            int(time.time()),
            rep_sig,
            root_id, rel_dir
        ))

    def update_child_dir_rep_cache_bulk(self, root_id: int, rel_dirs: Set[str]) -> None:
        """
        Updates representative cover cache for a bulk of directories.
        """
        for rel_dir in rel_dirs:
            self.update_dir_rep_cache(root_id, rel_dir)

    def update_book_hash(self, path: str, hash_val: Optional[str]) -> None:
        self._exec_write(
            "UPDATE books SET hash=? WHERE path=?",
            (hash_val, path)
        )


# -----------------------------
# Scan worker (Phase A)
# -----------------------------
class ScanSignals(QObject):
    progress = pyqtSignal(str)
    finished = pyqtSignal(int)
    error = pyqtSignal(str)

class ScanJob(QRunnable):
    def __init__(self, root_path: str, root_id: int, db: LibraryDB, auto_tag: bool = False, enable_hash: bool = False):
        super().__init__()
        self.root_path = norm(root_path)
        self.root_id = root_id
        self.db = db
        self.auto_tag = auto_tag
        self.enable_hash_scan = enable_hash
        self.signals = ScanSignals()
        self.touched_dirs: Set[str] = set() # To track directories that need cache update

    def _add_touched_dir(self, rel_dir: str):
        """Adds a directory and all its ancestors to the touched_dirs set."""
        current_dir = rel_dir
        while True:
            self.touched_dirs.add(current_dir)
            if not current_dir: # Reached root
                break
            current_dir = os.path.dirname(current_dir)
            if current_dir == ".": current_dir = "" # Handle os.path.dirname('.') == ''

    @staticmethod
    def _classify(path: str) -> Optional[str]:
        ext = os.path.splitext(path.lower())[1]
        if ext == ".zip":
            return "zip"
        if ext == ".pdf":
            return "pdf"
        return None

    def file_hash(self, path: str) -> Optional[str]:
        h = hashlib.sha1()
        try:
            with open(path, "rb") as f:
                while chunk := f.read(1024 * 1024):
                    h.update(chunk)
            return h.hexdigest()
        except Exception:
            return None

    def run(self) -> None:
        print(f"[SCAN] start {self.root_path}")
        start = time.perf_counter()
        try:
            count = 0
            err_count = 0
            dir_count = 0
            root = self.root_path
            
            batch = 0
            BATCH_N = 500

            with self.db._scan_lock:
                self.db.scan_conn.execute("BEGIN;")

            def _onerr(e: OSError):
                nonlocal err_count
                err_count += 1
                # 例: [Errno 5] Access is denied: '\\\\192...'
                self.signals.progress.emit(f"walk error({err_count}): {e}")

            for dirpath, dirnames, filenames in os.walk(root, onerror=_onerr):
                dir_count += 1
                if dir_count % 50 == 0:
                    self.signals.progress.emit(f"スキャン中… dirs={dir_count} files={count}")

                # --- ノイズフォルダは walk 対象から外す（in-place が重要）---
                dirnames[:] = [d for d in dirnames if d not in NOISE_DIR_NAMES and not d.startswith(".")]

                # そのディレクトリに zip/pdf が存在するか先に判定
                # has_books = any(self._classify(os.path.join(dirpath, fn)) for fn in filenames)

                try:
                    rel_dir = os.path.relpath(dirpath, root).replace("/", "\\")
                    if rel_dir == ".":
                        rel_dir = ""
                    parent_dir = os.path.dirname(rel_dir)
                    if parent_dir == ".":
                        parent_dir = ""
                    name = os.path.basename(rel_dir) if rel_dir else ""
                    # ノイズフォルダは dirs テーブルにも登録しない
                    if name in NOISE_DIR_NAMES or name.startswith("."):
                        continue
                    st_dir = os.stat(dirpath)
                    self.db.upsert_dir(
                        root_id=self.root_id,
                        rel_dir=rel_dir,
                        parent_dir=parent_dir,
                        name=name,
                        mtime=int(st_dir.st_mtime),
                        autocommit=False,
                        conn=self.db.scan_conn
                    ) # upsert_dir
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
                    if parent_dir == ".":
                        parent_dir = ""
                    title = os.path.splitext(os.path.basename(full))[0]

                    count += 1
                    if count % 20 == 0:
                        self.signals.progress.emit(f"スキャン中… {count} files / errors={err_count}")
                    
                    fhash = None

                    self.db.upsert_book(
                        path=norm(full),
                        root_id=self.root_id,
                        rel_path=rel,
                        parent_dir=parent_dir,
                        btype=btype,
                        size=int(st.st_size),
                        mtime=int(st.st_mtime),
                        title=title,
                        autocommit=False,
                        conn=self.db.scan_conn,
                        hash_val=fhash
                    ) # upsert_book

                    if self.auto_tag:
                        auto_tags = extract_auto_tags_from_title(title)
                        self.db.replace_auto_tags_for_book(
                            norm(full), auto_tags,
                            conn=self.db.scan_conn, autocommit=False
                        )

                    batch += 1

                    if batch >= BATCH_N:
                        with self.db._scan_lock:
                            self.db.scan_conn.commit()
                            self.db.scan_conn.execute("BEGIN;")
                        batch = 0

                    # Add the parent directory of the book to touched_dirs, and its ancestors
                    self._add_touched_dir(parent_dir)
            
            with self.db._scan_lock:
                self.db.scan_conn.commit()

            # Update representative cover cache for all touched directories
            self.db.update_child_dir_rep_cache_bulk(self.root_id, self.touched_dirs)
            self.signals.finished.emit(count)
            elapsed = time.perf_counter() - start
            print(f"[SCAN] finished {count} items in {elapsed:.1f}s")
        except Exception as e:
            # BEGIN中ならROLLBACKして接続状態を正常化
            try:
                with self.db._scan_lock:
                    self.db.scan_conn.rollback()
            except Exception:
                pass
            self.signals.error.emit(f"ScanJob fatal: {e}")


class LightScanSignals(QObject):
    progress = pyqtSignal(str)
    finished = pyqtSignal(str, int)   # rel_dir, added_or_updated_count
    error = pyqtSignal(str)

class LightScanJob(QRunnable):
    def __init__(self, root_path: str, root_id: int, rel_dir: str, db: LibraryDB, auto_tag: bool = False):
        super().__init__()
        self.root_path = norm(root_path)
        self.root_id = int(root_id)
        self.rel_dir = rel_dir or ""
        self.db = db
        self.auto_tag = auto_tag
        self.signals = LightScanSignals()

    @staticmethod
    def _classify(path: str) -> Optional[str]:
        ext = os.path.splitext(path.lower())[1]
        if ext == ".zip":
            return "zip"
        if ext == ".pdf":
            return "pdf"
        return None

    def run(self) -> None:
        try:
            abs_dir = norm(os.path.join(self.root_path, self.rel_dir)) if self.rel_dir else self.root_path
            if not os.path.isdir(abs_dir):
                self.signals.error.emit(f"フォルダが見つかりません: {abs_dir}")
                return

            changed = 0

            # 軽スキャンでもトランザクションを切る
            with self.db._scan_lock:
                self.db.scan_conn.execute("BEGIN;")

            try:
                # 直下だけ
                with os.scandir(abs_dir) as it:
                    entries = list(it)

                # 1) 直下サブフォルダ登録（孫は見ない）
                for ent in entries:
                    if not ent.is_dir(follow_symlinks=False):
                        continue
                    name = ent.name
                    if name in NOISE_DIR_NAMES or name.startswith("."):
                        continue

                    st = ent.stat(follow_symlinks=False)
                    child_rel = name if not self.rel_dir else (self.rel_dir + "\\" + name)
                    parent_dir = self.rel_dir

                    old = self.db.get_dir_row(self.root_id, child_rel)
                    old_mtime = int(old["mtime"]) if old else None
                    cur_mtime = int(st.st_mtime)

                    if old is None or old_mtime != cur_mtime:
                        self.db.upsert_dir(
                            root_id=self.root_id,
                            rel_dir=child_rel,
                            parent_dir=parent_dir,
                            name=name,
                            mtime=cur_mtime,
                            autocommit=False,
                            conn=self.db.scan_conn
                        )
                        changed += 1

                # 2) 直下 zip/pdf 登録
                for ent in entries:
                    if not ent.is_file(follow_symlinks=False):
                        continue

                    btype = self._classify(ent.name)
                    if not btype:
                        continue

                    st = ent.stat(follow_symlinks=False)
                    full = norm(ent.path)
                    rel_path = ent.name if not self.rel_dir else (self.rel_dir + "\\" + ent.name)
                    parent_dir = self.rel_dir
                    title = os.path.splitext(ent.name)[0]

                    old = self.db.get_book_brief(full)
                    cur_size = int(st.st_size)
                    cur_mtime = int(st.st_mtime)

                    if old and int(old["size"]) == cur_size and int(old["mtime"]) == cur_mtime:
                        continue

                    self.db.upsert_book(
                        path=full,
                        root_id=self.root_id,
                        rel_path=rel_path,
                        parent_dir=parent_dir,
                        btype=btype,
                        size=cur_size,
                        mtime=cur_mtime,
                        title=title,
                        autocommit=False,
                        conn=self.db.scan_conn,
                        hash_val=None
                    )

                    if self.auto_tag:
                        auto_tags = extract_auto_tags_from_title(title)
                        self.db.replace_auto_tags_for_book(
                            full, auto_tags,
                            conn=self.db.scan_conn, autocommit=False
                        )

                    changed += 1

                with self.db._scan_lock:
                    self.db.scan_conn.commit()

            except Exception:
                with self.db._scan_lock:
                    self.db.scan_conn.rollback()
                raise

            # このフォルダだけ代表キャッシュ更新
            self.db.update_single_dir_rep_cache(self.root_id, self.rel_dir)

            # 親（= 今表示している棚）の子フォルダ代表も変わりうるので親も更新
            parent_rel = os.path.dirname(self.rel_dir)
            if parent_rel == ".":
                parent_rel = ""
            self.db.update_single_dir_rep_cache(self.root_id, parent_rel)

            self.signals.finished.emit(self.rel_dir, changed)

        except Exception as e:
            self.signals.error.emit(str(e))


class DuplicateHashSignals(QObject):
    progress = pyqtSignal(str)
    finished = pyqtSignal(int)
    error = pyqtSignal(str)

class DuplicateHashJob(QRunnable):
    def __init__(self, db: LibraryDB, root_id: int):
        super().__init__()
        self.db = db
        self.root_id = root_id
        self.signals = DuplicateHashSignals()

    @staticmethod
    def file_hash(path: str) -> Optional[str]:
        h = hashlib.sha1()
        try:
            with open(path, "rb") as f:
                while True:
                    chunk = f.read(1024 * 1024)
                    if not chunk:
                        break
                    h.update(chunk)
            return h.hexdigest()
        except Exception:
            return None

    def run(self):
        try:
            with self.db._lock:
                cur = self.db.conn.cursor()
                cur.execute("""
                    SELECT path
                    FROM books
                    WHERE root_id=?
                      AND type IN ('zip','pdf')
                      AND hash IS NULL
                """, (self.root_id,))
                rows = cur.fetchall()

            total = len(rows)
            done = 0

            for r in rows:
                path = r["path"]
                hv = self.file_hash(path)
                self.db.update_book_hash(path, hv)
                done += 1
                if done % 20 == 0:
                    self.signals.progress.emit(f"重複チェック用ハッシュ計算中… {done}/{total}")

            self.signals.finished.emit(done)
        except Exception as e:
            self.signals.error.emit(str(e))


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
            if doc.page_count <= 0:
                raise RuntimeError("PDFにページがありません")

            page = doc.load_page(0)

            # 少し高めの解像度で描画
            mat = fitz.Matrix(1.8, 1.8)

            # 透明を消して安定化
            pix = page.get_pixmap(matrix=mat, alpha=False)

            im = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)

            # 白背景に近い余白を自動で少し削る
            im = im.convert("RGB")
            bg = Image.new("RGB", im.size, (255, 255, 255))
            diff = ImageChops.difference(im, bg)
            bbox = diff.getbbox()
            if bbox:
                # 余白を詰めすぎないよう少しマージンを残す
                left, top, right, bottom = bbox
                margin = 12
                left = max(0, left - margin)
                top = max(0, top - margin)
                right = min(im.width, right + margin)
                bottom = min(im.height, bottom + margin)
                im = im.crop((left, top, right, bottom))

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
    status_changed = pyqtSignal(int, int, int, int)

    def __init__(self, db: LibraryDB, cache_dir: str, pool: QThreadPool):
        super().__init__()
        self.db = db
        self.cache_dir = cache_dir
        self.pool = pool
        self.inflight: Set[str] = set()
        self.running = 0
        self.queue = deque()
        self.queued: Set[str] = set()
        self.req_count = 0
        self.hit_count = 0

    def request(self, path: str) -> None:
        self.req_count += 1
        path = norm(path)

        # 二重要求防止
        if path in self.inflight or path in self.queued:
            return

        # Manager側ではDBを叩かない。必要判定はThumbJob側でやる
        if self.running < MAX_THUMB_JOBS:
            self._start_job(path)
            self._emit_status()
            return

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
            self._start_job(nxt)
        
        self._emit_status()

    def clear_queue(self):
        self.queue.clear()
        self.queued.clear()
        self._emit_status()

    def _emit_status(self):
        self.status_changed.emit(len(self.queue), self.running, self.req_count, self.hit_count)

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


class TagManagerDialog(QDialog):
    def __init__(self, db: LibraryDB, parent=None):
        super().__init__(parent)
        self.db = db
        self.setWindowTitle("タグ管理")
        self.resize(300, 400)

        self.list = QListWidget()

        self.btn_add = QPushButton("追加")
        self.btn_del = QPushButton("削除")
        self.btn_rename = QPushButton("名前変更")
        self.btn_merge = QPushButton("統合")

        btns = QHBoxLayout()
        btns.addWidget(self.btn_add)
        btns.addWidget(self.btn_del)
        btns.addWidget(self.btn_rename)
        btns.addWidget(self.btn_merge)

        layout = QVBoxLayout(self)
        layout.addWidget(self.list)
        layout.addLayout(btns)

        self.btn_add.clicked.connect(self.add_tag)
        self.btn_del.clicked.connect(self.del_tag)
        self.btn_rename.clicked.connect(self.rename_tag)
        self.btn_merge.clicked.connect(self.merge_tag)

        self.reload()

    def reload(self):
        self.list.clear()
        for t in self.db.get_all_tags_with_count():
            name = t["name"]
            count = t["book_count"]
            item = QListWidgetItem(f"{name} ({count})")
            item.setData(Qt.ItemDataRole.UserRole, name)
            self.list.addItem(item)

    def add_tag(self):
        name, ok = QInputDialog.getText(self, "タグ追加", "タグ名")
        if ok and name:
            name = normalize_tag_name(name)
            if name:
                self.db.ensure_tag(name)
                self.reload()

    def del_tag(self):
        item = self.list.currentItem()
        if not item:
            return

        name = item.data(Qt.ItemDataRole.UserRole)
        tag_id = self.db.get_tag_id(name)
        if not tag_id:
            return

        ret = QMessageBox.question(
            self,
            "タグ削除",
            f"タグ「{name}」を削除しますか？\n"
            "このタグの本への紐付けも消えます。"
        )
        if ret != QMessageBox.StandardButton.Yes:
            return

        self.db.delete_tag(tag_id)
        self.reload()

    def rename_tag(self):
        item = self.list.currentItem()
        if not item:
            return

        old = item.data(Qt.ItemDataRole.UserRole)
        new, ok = QInputDialog.getText(self, "タグ名変更", "新しい名前", text=old)
        
        if ok and new:
            new = normalize_tag_name(new)
            if new and new != old:
                tag_id = self.db.get_tag_id(old)
                if tag_id:
                    self.db.rename_tag(tag_id, new)
                    self.reload()
            if not new or new == old:
                return

            existing_id = self.db.get_tag_id(new)
            old_id = self.db.get_tag_id(old)

            if existing_id and existing_id != old_id:
                QMessageBox.warning(
                    self,
                    "タグ名変更",
                    f"「{new}」は既に存在します。\n統合を使ってください。"
                )
                return

            if old_id:
                self.db.rename_tag(old_id, new)
                self.reload()

    def merge_tag(self):
        item = self.list.currentItem()
        if not item:
            QMessageBox.information(self, "タグ統合", "統合元タグを選択してください")
            return

        src_name = item.data(Qt.ItemDataRole.UserRole)

        all_names = []
        for i in range(self.list.count()):
            it = self.list.item(i)
            nm = it.data(Qt.ItemDataRole.UserRole)
            if nm != src_name:
                all_names.append(nm)

        if not all_names:
            QMessageBox.information(self, "タグ統合", "統合先にできるタグがありません")
            return

        dst_name, ok = QInputDialog.getItem(
            self,
            "タグ統合",
            f"「{src_name}」をどのタグへ統合しますか？",
            all_names,
            0,
            False
        )
        if not ok or not dst_name or dst_name == src_name:
            return

        src_id = self.db.get_tag_id(src_name)
        dst_id = self.db.get_tag_id(dst_name)
        if not src_id or not dst_id:
            QMessageBox.warning(self, "タグ統合", "タグIDの取得に失敗しました")
            return

        ret = QMessageBox.question(
            self,
            "タグ統合の確認",
            f"「{src_name}」を「{dst_name}」へ統合します。\n"
            f"この操作で {src_name} は削除されます。よろしいですか？"
        )
        if ret != QMessageBox.StandardButton.Yes:
            return

        self.db.merge_tags(src_id, dst_id)
        self.reload()

class TagEditDialog(QDialog):
    def __init__(self, db: LibraryDB, book_path: str, parent=None):
        super().__init__(parent)
        self.db = db
        self.book_path = book_path
        self.setWindowTitle("タグ編集")
        self.resize(400, 500)
        
        layout = QVBoxLayout(self)
        
        # 新規タグ入力
        h_new = QHBoxLayout()
        self.input_new = QLineEdit()
        self.input_new.setPlaceholderText("新規タグ名")
        btn_add = QPushButton("追加")
        btn_add.clicked.connect(self.add_new_tag)
        h_new.addWidget(self.input_new)
        h_new.addWidget(btn_add)
        layout.addLayout(h_new)
        
        # タグリスト
        self.list_widget = QListWidget()
        layout.addWidget(self.list_widget)
        
        # ボタン
        btns = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        btns.accepted.connect(self.accept)
        btns.rejected.connect(self.reject)
        layout.addWidget(btns)
        
        self.load_tags()

    def load_tags(self):
        self.list_widget.clear()
        all_tags = self.db.get_all_tags()
        # この本に付いているタグを取得
        current_tags_rows = self.db.get_tags_for_book(self.book_path)
        # source='manual' のものだけをチェック対象とする
        manual_tags = {r["name"] for r in current_tags_rows if r["source"] == "manual"}
        
        for row in all_tags:
            name = row["name"]
            item = QListWidgetItem(name)
            item.setFlags(item.flags() | Qt.ItemFlag.ItemIsUserCheckable)
            
            if name in manual_tags:
                item.setCheckState(Qt.CheckState.Checked)
            else:
                item.setCheckState(Qt.CheckState.Unchecked)
            
            self.list_widget.addItem(item)

    def add_new_tag(self):
        name = normalize_tag_name(self.input_new.text())
        if not name:
            return
        
        # DBに登録（ID確保）
        self.db.ensure_tag(name)
        
        # リストに存在しなければ追加、あればチェック
        items = self.list_widget.findItems(name, Qt.MatchFlag.MatchExactly)
        if items:
            item = items[0]
            item.setCheckState(Qt.CheckState.Checked)
            self.list_widget.scrollToItem(item)
        else:
            item = QListWidgetItem(name)
            item.setFlags(item.flags() | Qt.ItemFlag.ItemIsUserCheckable)
            item.setCheckState(Qt.CheckState.Checked)
            self.list_widget.addItem(item)
            self.list_widget.scrollToItem(item)
        
        self.input_new.clear()

    def get_checked_tags(self) -> List[str]:
        tags = []
        for i in range(self.list_widget.count()):
            item = self.list_widget.item(i)
            if item.checkState() == Qt.CheckState.Checked:
                tags.append(item.text())
        return tags


# -----------------------------
# Models
# -----------------------------
@dataclass
class BookItem:
    path: str
    title: str
    rel_path: str
    rating: int
    tags: List[str] = field(default_factory=list)

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
    tags: List[str] = field(default_factory=list)
    missing: bool = False


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
            tag_text = " ".join(f"#{t}" for t in item.tags)
            if tag_text:
                return f"{star}{item.title}\n{tag_text}"
            return f"{star}{item.title}"
        if role == Qt.ItemDataRole.ToolTipRole:
            tag_text = " ".join(f"#{t}" for t in item.tags)
            return f"{item.rel_path}\nRating: {item.rating}\nTags: {tag_text}"
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
                prefix = "× " if item.missing else "📁 "
                return f"{star}{prefix}{label}"
            # book
            tag_text = " ".join(f"#{t}" for t in item.tags)
            if tag_text:
                return f"{star}{label}\n{tag_text}"
            return f"{star}{label}"

        if role == Qt.ItemDataRole.ToolTipRole:
            base_text = f"{item.tooltip}\nRating: {item.rating}"
            if item.kind == "dir" and item.missing:
                return base_text + "\nフォルダが見つかりません"
            if item.kind == "book":
                tag_text = " ".join(f"#{t}" for t in item.tags)
                return f"{base_text}\nTags: {tag_text}"
            return base_text

        if role == Qt.ItemDataRole.ForegroundRole:
            if getattr(item, "missing", False):
                return QColor(140, 140, 140)

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

    def update_dir_rep(self, rel_dir: str, rep_path: str, rating: int) -> None:
        for i, item in enumerate(self.items):
            if item.kind == "dir" and item.rel_dir == rel_dir:
                new_item = MixedItem(
                    kind="dir",
                    title=item.title,
                    tooltip=item.tooltip,
                    rel_dir=item.rel_dir,
                    rep_path=rep_path,
                    rating=rating
                )
                self.items[i] = new_item
                idx = self.index(i)
                self.dataChanged.emit(idx, idx, [Qt.ItemDataRole.DecorationRole, Qt.ItemDataRole.DisplayRole])
                break

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
        self.auto_tag_enabled = self.settings.value("auto_tag_enabled", AUTO_TAG_ENABLED_DEFAULT, type=bool)
        self.auto_light_scan_on_enter = self.settings.value("auto_light_scan_on_enter", AUTO_LIGHT_SCAN_ON_ENTER_DEFAULT, type=bool)
        self._light_scan_last: Dict[str, float] = {}
        self._light_scan_running: Set[str] = set()
        self.min_rating = 0
        self.show_redraw_log = False  # 再描画ログの表示設定（デフォルト非表示）
        
        self._typeahead = ""
        self._typeahead_timer = QTimer(self)
        self._typeahead_timer.setSingleShot(True)
        self._typeahead_timer.timeout.connect(self._clear_typeahead)

        self.icons = IconCache()
        self.thumb = ThumbManager(self.db, self.cache_dir, self.pool)
        self.thumb.thumb_ready.connect(self._on_thumb_ready)
        

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
        self.view_mode = "normal"
        self.current_dir_rel = ""   # "" がルート
        self._scroll_pos = {}  # key: (dir_rel, mode_index) -> (scroll_val, anchor)
        self._scan_running = False
        self._scan_job = None

        # フォルダ代表表紙キャッシュ（検索なしの棚表示用）
        # key: (root_id, parent_dir_rel, only_star)
        self._dir_rep_cache: Dict[Tuple[int, str, bool], Dict[str, Tuple[str, int]]] = {}
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

        self.search = QLineEdit()
        self.search.setPlaceholderText("検索（タイトル/パス）")
        top.addWidget(self.search, 2)

        self.combo_tag = QComboBox()
        self.combo_tag.addItem("タグ")
        self.combo_tag.currentIndexChanged.connect(self.refresh_view)
        top.addWidget(self.combo_tag, 0)

        self.btn_tag_mgr = QPushButton("タグ管理")
        self.btn_tag_mgr.clicked.connect(self.open_tag_manager)
        top.addWidget(self.btn_tag_mgr, 0)

        self.chk_auto_tag = QCheckBox("自動タグ")
        self.chk_auto_tag.setChecked(self.auto_tag_enabled)
        self.chk_auto_tag.stateChanged.connect(self._toggle_auto_tag)
        top.addWidget(self.chk_auto_tag, 0)

        self.chk_light_scan = QCheckBox("フォルダ自動")
        self.chk_light_scan.setChecked(self.auto_light_scan_on_enter)
        self.chk_light_scan.stateChanged.connect(self._toggle_light_scan)
        top.addWidget(self.chk_light_scan, 0)

        # 棚/フラットは2択なのでトグルにする（OFF=棚, ON=フラット）
        self.btn_mode = QPushButton("棚")
        self.btn_mode.setCheckable(True)
        self.btn_mode.setChecked(False)
        self.btn_mode.toggled.connect(self._on_mode_toggled)
        top.addWidget(self.btn_mode, 0)
        QShortcut(QKeySequence("F"), self, activated=self.btn_mode.toggle)

        self.btn_star_filter = QPushButton("☆")
        self.btn_star_filter.setCheckable(True)
        self.btn_star_filter.setFixedWidth(40)
        self.btn_star_filter.setStyleSheet("color: #888888; font-size: 16px; font-weight: bold;")
        self.btn_star_filter.toggled.connect(self._toggle_star_filter)
        top.addWidget(self.btn_star_filter, 0)

        self.btn_recent = QPushButton("最近")
        self.btn_recent.setCheckable(True)
        self.btn_recent.clicked.connect(self.show_recent)
        top.addWidget(self.btn_recent, 0)

        self.btn_unread = QPushButton("未読")
        self.btn_unread.setCheckable(True)
        self.btn_unread.clicked.connect(self.show_unread)
        top.addWidget(self.btn_unread, 0)

        self.btn_duplicates = QPushButton("重複")
        self.btn_duplicates.setCheckable(True)
        self.btn_duplicates.clicked.connect(self.show_duplicates)
        top.addWidget(self.btn_duplicates, 0)

        self.btn_dup_hash = QPushButton("重複ハッシュ作成")
        self.btn_dup_hash.clicked.connect(self.build_duplicate_hashes)
        top.addWidget(self.btn_dup_hash, 0)

        self.btn_root = QPushButton("📚本棚")
        self.btn_root.clicked.connect(self.show_root)
        top.addWidget(self.btn_root, 0)

        self.btn_change_root = QPushButton("本棚変更")
        self.btn_change_root.clicked.connect(self.choose_root)
        top.addWidget(self.btn_change_root, 0)
        
        self.btn_scan = QPushButton("更新")
        top.addWidget(self.btn_scan, 0)
        
        self.btn_redraw = QPushButton("再表示")
        top.addWidget(self.btn_redraw, 0)
        
        self.btn_open = QPushButton("外部")
        top.addWidget(self.btn_open, 0)
        
        self.btn_memo = QPushButton("メモ取込")
        self.btn_memo.clicked.connect(self.sync_memo)
        top.addWidget(self.btn_memo, 0)

        # 現在地バー（HTMLカラー表示用）
        self.loc_bar = QLabel("")
        self.loc_bar.setTextFormat(Qt.TextFormat.RichText)
        self.loc_bar.setTextInteractionFlags(Qt.TextInteractionFlag.TextBrowserInteraction)
        self.loc_bar.setOpenExternalLinks(False)
        self.loc_bar.linkActivated.connect(self._on_loc_link)
        self.loc_bar.setStyleSheet("""
        QLabel {
          background: qlineargradient(x1:0,y1:0,x2:1,y2:0, stop:0 #1f2937, stop:1 #111827);
          border: 1px solid #2f3136;
          border-radius: 10px;
          padding: 7px 10px;
        }
        """)
        v.addWidget(self.loc_bar)

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

        self.btn_scan.clicked.connect(self.scan)
        self.btn_redraw.clicked.connect(self.force_redraw_visible)
        self.search.textChanged.connect(self.refresh_view)
        self.btn_open.clicked.connect(self.open_external)
        self.btn_back.clicked.connect(self.nav_back)
        self.btn_up.clicked.connect(self.nav_up)
        self.view.doubleClicked.connect(self._on_item_activated)

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
            self.setWindowTitle(f"{APP_NAME} (Bookshelf.py)  —  {self.root_path}")
            self.statusBar().showMessage(f"ROOT: {self.root_path}")
            self.refresh_view()
            
            self.thumb.clear_queue()
        else:
            roots = self.db.get_roots()
            if roots:
                self.set_root(roots[0])

        self.update_tag_list()

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

    def show_root(self):
        self._clear_filter_buttons()
        self.view_mode = "normal"
        self.current_dir_rel = ""
        self.refresh_view()

    def _clear_filter_buttons(self):
        self.btn_recent.setChecked(False)
        self.btn_unread.setChecked(False)
        self.btn_duplicates.setChecked(False)

    def show_normal(self):
        self._clear_filter_buttons()
        self.view_mode = "normal"
        self.thumb.clear_queue()
        self.refresh_view()
        self._schedule_auto_redraw(1000)

    def show_recent(self):
        self._clear_filter_buttons()
        self.btn_recent.setChecked(True)
        self.view_mode = "recent"
        self.thumb.clear_queue()
        self.refresh_view()
        self._schedule_auto_redraw(1000)

    def show_unread(self):
        self._clear_filter_buttons()
        self.btn_unread.setChecked(True)
        self.view_mode = "unread"
        self.thumb.clear_queue()
        self.refresh_view()
        self._schedule_auto_redraw(1000)

    def show_duplicates(self):
        self._clear_filter_buttons()
        self.btn_duplicates.setChecked(True)
        self.view_mode = "duplicates"
        self.thumb.clear_queue()
        self.refresh_view()
        self._schedule_auto_redraw(1000)

    def set_root(self, path: str):
        self.root_path = norm(path)
        self.root_id = self.db.upsert_root(self.root_path)
        self.view_mode = "normal"
        self.current_dir_rel = ""
        self._scroll_pos.clear()
        
        self.settings.setValue("last_root", self.root_path)
        self.settings.setValue("last_dir", "")

        self.setWindowTitle(f"{APP_NAME} (Bookshelf.py)  —  {self.root_path}")
        self.statusBar().showMessage(f"ROOT: {self.root_path}")
        self.refresh_view()
        
        self.thumb.clear_queue()

        self._schedule_auto_redraw(1000)

    def _mode_index(self) -> int:
        # 0 = 棚（混在）, 1 = フラット（配下すべて）
        return 1 if self.btn_mode.isChecked() else 0

    def _on_mode_toggled(self, checked: bool):
        self.view_mode = "normal"
        self.btn_mode.setText("フラット" if checked else "棚")
        self.refresh_view()

    def _toggle_star_filter(self, checked: bool):
        if checked:
            self.btn_star_filter.setText("★")
            self.btn_star_filter.setStyleSheet("color: #FFD700; font-size: 16px; font-weight: bold;")
            self.min_rating = 1
        else:
            self.btn_star_filter.setText("☆")
            self.btn_star_filter.setStyleSheet("color: #888888; font-size: 16px; font-weight: bold;")
            self.min_rating = 0
        self.refresh_view()

    def _get_tag_filter(self) -> str:
        txt = self.combo_tag.currentText()
        if txt == "タグ" or not txt:
            return ""
        return txt

    def update_tag_list(self):
        current = self.combo_tag.currentText()
        self.combo_tag.blockSignals(True)
        self.combo_tag.clear()
        self.combo_tag.addItem("タグ")
        tags = self.db.get_all_tags()
        for t in tags:
            self.combo_tag.addItem(t["name"])
        
        idx = self.combo_tag.findText(current)
        if idx >= 0:
            self.combo_tag.setCurrentIndex(idx)
        self.combo_tag.blockSignals(False)

    def sync_memo(self):
        if not self.root_id:
            QMessageBox.information(self, "Memo", "先にルートを選択してください")
            return

        path = MEMO_FILE_PATH
        if not os.path.exists(path):
            QMessageBox.warning(self, "Memo", f"favorite.txt が見つかりません:\n{path}")
            return

        try:
            authors: Set[str] = set()

            with open(path, "r", encoding="utf-8") as f:
                for line in f:
                    author = extract_first_bracket_author(line)
                    if author:
                        authors.add(author)

            if not authors:
                QMessageBox.information(self, "Memo", "メモ内に作者名 [ ] が見つかりませんでした")
                return

            count = self.db.star_root_author_dirs(self.root_id, authors)

            self._dir_rep_cache.clear()
            self.refresh_view()
            self.statusBar().showMessage(f"メモ取込: 作者 {len(authors)} 件 / ★付与 {count} フォルダ", 5000)

        except Exception as e:
            QMessageBox.warning(self, "Memo Error", str(e))

    def _update_thumb_status(self, q, r, req, hit):
        self.thumb_status_lbl.setText(f"Thumb: Q={q} Run={r} Req={req} Hit={hit}")

    def force_redraw_visible(self):
        if self.show_redraw_log:
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

    def _toggle_auto_tag(self, state):
        self.auto_tag_enabled = bool(state)
        self.settings.setValue("auto_tag_enabled", self.auto_tag_enabled)

    def _toggle_light_scan(self, state):
        self.auto_light_scan_on_enter = bool(state)
        self.settings.setValue("auto_light_scan_on_enter", self.auto_light_scan_on_enter)

    def _maybe_start_light_scan_for_dir(self, rel_dir: str):
        if not self.root_path or not self.root_id:
            return
        if not rel_dir:
            # ルートでは自動軽スキャンしない
            return
        if not self.auto_light_scan_on_enter:
            return
        if self.view_mode != "normal":
            return

        now = time.time()
        last = self._light_scan_last.get(rel_dir, 0.0)
        if now - last < LIGHT_SCAN_RESCAN_SECONDS:
            return

        if rel_dir in self._light_scan_running:
            return

        self._light_scan_last[rel_dir] = now
        self._light_scan_running.add(rel_dir)

        job = LightScanJob(
            self.root_path,
            self.root_id,
            rel_dir,
            self.db,
            auto_tag=self.auto_tag_enabled
        )

        def on_finished(done_rel: str, changed: int):
            self._light_scan_running.discard(done_rel)

            # いま見ているフォルダと一致する時だけ再表示
            if self.current_dir_rel == done_rel:
                self._dir_rep_cache.clear()
                self.refresh_view()
                if changed > 0:
                    self.statusBar().showMessage(f"フォルダ自動更新: {changed} 件反映", 3000)

        def on_error(msg: str):
            self._light_scan_running.discard(rel_dir)
            self.statusBar().showMessage(f"フォルダ自動更新エラー: {msg}", 4000)

        job.signals.finished.connect(on_finished)
        job.signals.error.connect(on_error)
        self.pool.start(job)

    def scan(self):
        if not self.root_path or not self.root_id:
            QMessageBox.information(self, "Info", "先にルートを選択してね")
            return

        self._scan_running = True
        self.statusBar().showMessage("スキャン開始…")

        job = ScanJob(self.root_path, self.root_id, self.db, auto_tag=self.auto_tag_enabled)
        self._scan_job = job

        def on_progress(msg: str):
            self.statusBar().showMessage(msg)

        def on_finished(c: int):
            self._scan_running = False
            self._dir_rep_cache.clear()
            self.refresh_view()
            QTimer.singleShot(0, lambda: self.statusBar().showMessage(f"スキャン完了: {c} files"))

        def on_error(e: str):
            self._scan_running = False
            QMessageBox.critical(self, "Scan Error", e)

        job.signals.progress.connect(on_progress)
        job.signals.finished.connect(on_finished)
        job.signals.error.connect(on_error)

        self.pool.start(job)

    def build_duplicate_hashes(self):
        if not self.root_id:
            return

        self.statusBar().showMessage("重複チェック用ハッシュ計算開始…")
        job = DuplicateHashJob(self.db, self.root_id)

        def on_progress(msg: str):
            self.statusBar().showMessage(msg)

        def on_finished(c: int):
            self.statusBar().showMessage(f"重複チェック用ハッシュ計算完了: {c} files")
            if self.view_mode == "duplicates":
                self.refresh_view()

        def on_error(msg: str):
            QMessageBox.critical(self, "Duplicate Hash Error", msg)

        job.signals.progress.connect(on_progress)
        job.signals.finished.connect(on_finished)
        job.signals.error.connect(on_error)
        self.pool.start(job)

    def refresh(self):
        self.refresh_view()

    def _need_tags_for_view(self, min_rating: int, tag_filter: str) -> bool:
        # タグ絞り込み中は必要
        if tag_filter:
            return True
        # ☆だけ見たい時は速度優先で省略
        if min_rating >= 1:
            return False
        return True

    def refresh_view(self):
        t_total0 = time.perf_counter()
        if not self.root_id:
            return
        
        self.settings.setValue("last_dir", self.current_dir_rel)

        # Update UI for current location
        crumb = self._crumb()
        self.setWindowTitle(f"{APP_NAME} (Bookshelf.py) — {crumb}")
        self.loc_bar.setText(self._loc_text())

        q = self.search.text()
        min_rating = self.min_rating
        tag_filter = self._get_tag_filter()

        dir_items = []
        book_items = []
        items = []

        # --- ① SQL ---
        t_sql0 = time.perf_counter()

        if self.view_mode == "recent":
            # 最近追加ビュー
            rows = self.db.list_recent_books(self.root_id, limit=200)
            sql_time = (time.perf_counter() - t_sql0) * 1000

            # --- ② UI ---
            t_ui0 = time.perf_counter()
            paths = [r["path"] for r in rows]
            need_tags = self._need_tags_for_view(min_rating, tag_filter)
            tags_map = self.db.get_tags_bulk_for_paths(paths) if need_tags else {}
            items = [BookItem(path=r["path"], title=r["title"], rel_path=r["rel_path"], rating=int(r["rating"]), tags=tags_map.get(r["path"], [])) for r in rows]
            self.book_model.set_items(items)
            self.view.setModel(self.book_model)
            ui_time = (time.perf_counter() - t_ui0) * 1000

        elif self.view_mode == "unread":
            # 未閲覧ビュー
            rows = self.db.list_unread_books(self.root_id)
            sql_time = (time.perf_counter() - t_sql0) * 1000

            # --- ② UI ---
            t_ui0 = time.perf_counter()
            paths = [r["path"] for r in rows]
            need_tags = self._need_tags_for_view(min_rating, tag_filter)
            tags_map = self.db.get_tags_bulk_for_paths(paths) if need_tags else {}
            items = [BookItem(path=r["path"], title=r["title"], rel_path=r["rel_path"], rating=int(r["rating"]), tags=tags_map.get(r["path"], [])) for r in rows]
            self.book_model.set_items(items)
            self.view.setModel(self.book_model)
            ui_time = (time.perf_counter() - t_ui0) * 1000

        elif self.view_mode == "duplicates":
            # 重複本ビュー
            rows = self.db.list_duplicate_books(self.root_id)
            sql_time = (time.perf_counter() - t_sql0) * 1000

            # --- ② UI ---
            t_ui0 = time.perf_counter()
            paths = [r["path"] for r in rows]
            need_tags = self._need_tags_for_view(min_rating, tag_filter)
            tags_map = self.db.get_tags_bulk_for_paths(paths) if need_tags else {}
            items = [BookItem(path=r["path"], title=f"[{r['hash'][:6]}] {r['title']}", rel_path=r["rel_path"], rating=int(r["rating"]), tags=tags_map.get(r["path"], [])) for r in rows]
            self.book_model.set_items(items)
            self.view.setModel(self.book_model)
            ui_time = (time.perf_counter() - t_ui0) * 1000

        elif self._mode_index() == 1:
            # フラット（配下すべて）
            rows = self.db.list_books_recursive(self.root_id, self.current_dir_rel, query=q, min_rating=min_rating, tag_filter=tag_filter)
            sql_time = (time.perf_counter() - t_sql0) * 1000

            # --- ② UI ---
            t_ui0 = time.perf_counter()
            paths = [r["path"] for r in rows]
            need_tags = self._need_tags_for_view(min_rating, tag_filter)
            tags_map = self.db.get_tags_bulk_for_paths(paths) if need_tags else {}
            items = [BookItem(path=r["path"], title=r["title"], rel_path=r["rel_path"], rating=int(r["rating"]), tags=tags_map.get(r["path"], [])) for r in rows]
            self.book_model.set_items(items)
            self.view.setModel(self.book_model)
            ui_time = (time.perf_counter() - t_ui0) * 1000

        else:
            # 棚（混在）
            dir_rows = self.db.list_child_dirs(self.root_id, parent_dir=self.current_dir_rel, query=q, min_rating=min_rating, tag_filter=tag_filter)
            book_rows = self.db.list_direct_books(self.root_id, dir_rel=self.current_dir_rel, query=q, min_rating=min_rating, tag_filter=tag_filter)
            
            # 代表表紙：検索なしの通常表示だけキャッシュ（検索中は毎回算出）

            rep_map: Dict[str, Tuple[str, int]] = {}
            q_str = (q or "").strip()
            if q_str == "":
                key = (int(self.root_id), self.current_dir_rel, bool(min_rating >= 1))
                rep_map = self._dir_rep_cache.get(key)
                if rep_map is None:
                    rep_map = self.db.get_child_dir_rep_cache(
                        self.root_id,
                        parent_dir=self.current_dir_rel,
                        only_star=(min_rating >= 1)
                    )

                    # 起動時/表示時には重い再構築をしない
                    self._dir_rep_cache[key] = rep_map
            else:
                rep_map = self.db.list_child_dir_reps(
                    self.root_id,
                    parent_dir=self.current_dir_rel,
                    query=q_str,
                    only_star=(min_rating >= 1)
                )
            sql_time = (time.perf_counter() - t_sql0) * 1000

            # --- ② UI ---
            t_ui0 = time.perf_counter()

            book_paths = [r["path"] for r in book_rows]
            need_tags = self._need_tags_for_view(min_rating, tag_filter)
            tags_map = self.db.get_tags_bulk_for_paths(book_paths) if need_tags else {}

            for d in dir_rows:
                rel_dir = d["rel_dir"]
                name = d["name"]
                dir_star = int(d["rating"])

                rep = rep_map.get(name)
                rep_path = rep[0] if rep else ""
                rep_rating = int(rep[1]) if rep else 0

                # キャッシュが空なら、そのフォルダだけ代表を計算して使う
                if not rep_path:
                    rep2 = self.db.get_dir_rep_path(self.root_id, rel_dir, only_star=(min_rating >= 1))
                    if rep2:
                        rep_path = rep2[0]
                        rep_rating = int(rep2[1])
                        self.db.update_single_dir_rep_cache(self.root_id, rel_dir)

                shown_rating = max(dir_star, rep_rating)

                dir_items.append(MixedItem(
                    kind="dir",
                    title=name if name else "(root)",
                    tooltip=self._crumb_for(rel_dir),
                    rel_dir=rel_dir,
                    rep_path=rep_path,
                    rating=shown_rating
                ))

            for r in book_rows:
                book_items.append(MixedItem(
                    kind="book",
                    title=r["title"],
                    tooltip=r["rel_path"],
                    path=r["path"],
                    rel_path=r["rel_path"],
                    rating=int(r["rating"]),
                    tags=tags_map.get(r["path"], [])
                ))

            items = (dir_items + book_items) if SHOW_DIRS_FIRST else (book_items + dir_items)
            self.mixed_model.set_items(items)
            self.view.setModel(self.mixed_model)
            
            ui_time = (time.perf_counter() - t_ui0) * 1000

        # --- Total & Status ---
        total_time = (time.perf_counter() - t_total0) * 1000

        if not self._scan_running:
            if self.view_mode == "recent":
                status_prefix = "最近追加 (200件)"
                d_count = 0
                b_count = len(items)
            elif self.view_mode == "unread":
                status_prefix = "未閲覧"
                d_count = 0
                b_count = len(items)
            elif self.view_mode == "duplicates":
                status_prefix = "重複本"
                d_count = 0
                b_count = len(items)
            elif self._mode_index() == 1:
                status_prefix = "フラット" + (f" (Min:{min_rating})" if min_rating > 0 else "") + (f" [Tag:{tag_filter}]" if tag_filter else "")
                d_count = 0
                b_count = len(items)
            else:
                status_prefix = "棚（混在）" + (f" (Min:{min_rating})" if min_rating > 0 else "") + (f" [Tag:{tag_filter}]" if tag_filter else "")
                d_count = len(dir_items)
                b_count = len(book_items)

            self.statusBar().showMessage(
                f"{status_prefix} dirs={d_count} books={b_count} "
                f"sql={sql_time:.1f}ms "
                f"ui={ui_time:.1f}ms "
                f"total={total_time:.1f}ms"
            )

        # 直後はレイアウト未確定があるので、少し遅延して確実にprefetch
        QTimer.singleShot(0, self.view.doItemsLayout)
        QTimer.singleShot(60, self._restore_scroll)

    def _selected_book_path(self) -> Optional[str]:
        kind, path, _rel = self._selected_item()
        return path if kind == "book" else None

    def toggle_star(self):
        kind, path, rel_dir = self._selected_item()
        if not kind:
            return

        if kind == "dir":
            cur = self.db.get_dir_rating(self.root_id, rel_dir)
            new = 0 if cur > 0 else 1
            self.db.set_dir_rating(self.root_id, rel_dir, new)

            self.thumb.clear_queue()
            self.refresh_view()
            self._schedule_auto_redraw(1000)
            return

        # book
        if not path:
            return

        cur = self.db.get_rating(path)
        new = 0 if cur > 0 else 1
        self.db.set_rating(path, new)

        info = self.db.get_thumb_info(path)
        thumb_path = info["cover_thumb_path"] if info else None
        self.icons.drop(thumb_path)

        self.thumb.clear_queue()
        self.refresh_view()
        self._schedule_auto_redraw(1000)

    def hide_book(self):
        kind, path, _ = self._selected_item()
        if kind == "book" and path:
            self.db.set_rating(path, -1)
            self.refresh_view()

    def edit_tags(self):
        path = self._selected_book_path()
        if not path:
            return
        
        dlg = TagEditDialog(self.db, path, self)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            new_tags = dlg.get_checked_tags()
            self.db.set_book_tags(path, new_tags, source="manual")
            self.update_tag_list() # タグが増えたかもしれないので更新
            self.statusBar().showMessage("タグを更新しました")

    def open_tag_manager(self):
        dlg = TagManagerDialog(self.db, self)
        dlg.exec()
        self.update_tag_list()
        self.refresh_view()

    def open_external(self):
        path = self._selected_book_path()
        if not path:
            return
        self._open_in_honeyview(path)

    def _open_in_honeyview(self, path: str) -> None:
        ext = os.path.splitext(path)[1].lower()

        # PDFは既定アプリで開く
        if ext == ".pdf":
            try:
                os.startfile(path)  # Windows専用
                self.db.mark_opened(path)
                return
            except Exception as e:
                QMessageBox.critical(self, "Viewer Error", f"PDF起動に失敗:\n{e}")
                return

        # zip / img は Honeyview
        if not os.path.exists(VIEWER_EXE):
            QMessageBox.critical(self, "Viewer Error", f"Honeyview が見つからない:\n{VIEWER_EXE}")
            return
        try:
            subprocess.Popen([VIEWER_EXE, path], shell=False)
            self.db.mark_opened(path)
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
            cur = self.db.get_dir_rating(self.root_id, sel_rel_dir)
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
            
            act_hide = QAction("本を隠す (Rating -1)", self)
            act_hide.triggered.connect(self.hide_book)
            menu.addAction(act_hide)

            act_tag = QAction("タグを編集...", self)
            act_tag.triggered.connect(self.edit_tags)
            menu.addAction(act_tag)

            act_tag_mgr = QAction("タグ管理...", self)
            act_tag_mgr.triggered.connect(self.open_tag_manager)
            menu.addAction(act_tag_mgr)
            menu.addSeparator()

        menu.exec(self.view.viewport().mapToGlobal(pos))

    def _enter_dir(self, rel_dir: str):
        abs_dir = self._abs_dir(rel_dir)
        if not os.path.isdir(abs_dir):
            self._mark_dir_missing(rel_dir)
            self.statusBar().showMessage("フォルダが見つかりません")
            self.view.viewport().update()
            return

        self._save_scroll()
        self.current_dir_rel = rel_dir

        # ★のみでフォルダカードから入ったら、中では全表示に戻す
        if self.view_mode == "normal" and self.min_rating >= 1:
            self.min_rating = 0
            self.btn_star_filter.blockSignals(True)
            self.btn_star_filter.setChecked(False)
            self.btn_star_filter.setText("☆")
            self.btn_star_filter.setStyleSheet("color: #888888; font-size: 16px; font-weight: bold;")
            self.btn_star_filter.blockSignals(False)

        self.refresh_view()
        # フォルダ移動直後はレイアウト未確定で可視判定が漏れることがあるので保険を打つ
        self.thumb.clear_queue()
        self._schedule_auto_redraw(1000)
        self._maybe_start_light_scan_for_dir(rel_dir)

    def _mark_dir_missing(self, rel_dir: str):
        model = self.view.model()
        if not isinstance(model, MixedListModel):
            return

        for i, item in enumerate(model.items):
            if item.kind == "dir" and item.rel_dir == rel_dir:
                item.missing = True
                idx = model.index(i, 0)
                model.dataChanged.emit(idx, idx)
                break

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
        if isinstance(model, BookListModel):
            model.notify_thumb_ready_hit(path)
        elif isinstance(model, FolderListModel):
            model.notify_thumb_ready_hit(path)
        elif isinstance(model, MixedListModel):
            model.notify_thumb_ready_hit(path)
        
        self.view.viewport().update()

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

    def _rel_parts(self) -> List[str]:
        rel = (self.current_dir_rel or "").strip("\\/")
        if not rel:
            return []
        return rel.split("\\")

    def _on_loc_link(self, href: str) -> None:
        # href 例: "loc:root" / "loc:dir:A\B"
        if not href.startswith("loc:"):
            return

        target = href[4:]
        if target == "root":
            self.view_mode = "normal"
            if self.current_dir_rel != "":
                self._save_scroll()
            self.current_dir_rel = ""
            self.refresh_view()
            return

        if target.startswith("dir:"):
            rel = target[4:]
            # 同じ場所を押しても無駄にrefreshしない
            if rel != self.current_dir_rel:
                self._save_scroll()
                self.current_dir_rel = rel
                self.refresh_view()

    def _loc_text(self) -> str:
        if not self.root_path:
            return "ROOT: (no root)"

        root_name = os.path.basename(self.root_path.rstrip("\\/")) or self.root_path

        # ROOT（青）をクリック可能に
        root_html = (
            f'<a href="loc:root" style="text-decoration:none; color:#e5e7eb;;">'
            f'<span style="color:#7dd3fc; font-weight:800;">ROOT</span>: {root_name}'
            f'</a>'
        )

        parts = self._rel_parts()
        if not parts:
            return root_html

        def link(rel: str, text: str, is_current: bool) -> str:
            if is_current:
                return (
                    f'<a href="loc:dir:{rel}" style="text-decoration:none;">'
                    f'<span style="color:#a3e635; font-weight:800;">{text}</span>'
                    f'</a>'
                )
            return f'<a href="loc:dir:{rel}" style="text-decoration:none;">{text}</a>'

        # 1階層
        if len(parts) == 1:
            a = parts[0]
            return root_html + "  ›  " + link(a, a, True)

        # 2階層（想定の主戦場）
        if len(parts) == 2:
            a, b = parts
            return root_html + "  ›  " + link(a, a, False) + "  ›  " + link(a + "\\" + b, b, True)

        # 3階層以上（レアなので省略）
        a = parts[0]
        c = parts[-1]
        rel_a = a
        rel_c = "\\".join(parts)

        # "…" はクリック無効でOK（見た目の区切り）
        dots = '<span style="color:#9ca3af;">…</span>'

        return root_html + "  ›  " + link(rel_a, a, False) + f"  ›  {dots}  ›  " + link(rel_c, c, True)

    def _rep_path_for_current(self) -> str:
        rows = self.db.list_books(self.root_id, query="", min_rating=0, dir_rel=self.current_dir_rel)
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
        self.view_mode = "normal"
        self._save_scroll()
        self.current_dir_rel = child if not self.current_dir_rel else (self.current_dir_rel + "\\" + child)

        # ★のみでフォルダカードから入ったら、中では全表示に戻す
        if self.min_rating >= 1:
            self.min_rating = 0
            self.btn_star_filter.blockSignals(True)
            self.btn_star_filter.setChecked(False)
            self.btn_star_filter.setText("☆")
            self.btn_star_filter.setStyleSheet("color: #888888; font-size: 16px; font-weight: bold;")
            self.btn_star_filter.blockSignals(False)

        self.refresh_view()
        self._schedule_auto_redraw(1000)

    def nav_up(self):
        if not self.current_dir_rel:
            return
        self.view_mode = "normal"
        self._save_scroll()
        self.current_dir_rel = os.path.dirname(self.current_dir_rel)
        if self.current_dir_rel == ".":
            self.current_dir_rel = ""
        self.refresh_view()
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

    def _clear_typeahead(self):
        self._typeahead = ""

    def _handle_typeahead(self, text: str):
        self._typeahead += text
        self._typeahead_timer.start(700) # 700ms reset
        
        # Search in model
        model = self.view.model()
        if not model: return
        
        search_term = self._typeahead.lower()
        # 現在位置の次から検索開始（連続入力で次へ次へと飛べるように）
        start_row = self.view.currentIndex().row() + 1
        if start_row >= model.rowCount(): start_row = 0
        
        # Wrap around search
        for i in range(model.rowCount()):
            idx = (start_row + i) % model.rowCount()
            item = model.items[idx]
            
            # タイトルの先頭一致を確認
            title = ""
            if hasattr(item, "title"): title = item.title
            elif hasattr(item, "child"): title = item.child
            
            if title.lower().startswith(search_term):
                qidx = model.index(idx, 0)
                self.view.setCurrentIndex(qidx)
                self.view.scrollTo(qidx)
                return

    def eventFilter(self, source, event: QEvent):
        """リストビュー上でのマウス操作を監視"""
        if source is self.view or source is self.view.viewport():
            if event.type() == QEvent.Type.MouseButtonPress:
                # XButton1 はチルト左 / 戻るボタン
                if event.button() == Qt.MouseButton.XButton1:
                    self.nav_back()
                    return True  # イベントを消費
            
            elif event.type() == QEvent.Type.KeyPress:
                text = event.text()
                if text and text.isprintable() and not (event.modifiers() & (Qt.KeyboardModifier.ControlModifier | Qt.KeyboardModifier.AltModifier)):
                    self._handle_typeahead(text)
                    return True # Consume event to prevent default jump

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
