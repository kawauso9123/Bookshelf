# 📚 Bookshelf

Bookshelf は、ローカル / NAS 上の自炊書籍（画像フォルダ・ZIP・PDF）をサムネイル付きで管理・閲覧できる **PyQt6 製デスクトップ本棚アプリ**です。SQLite にメタデータを保存するため、検索・絞り込み・お気に入り管理を軽快に行えます。

## 主な機能

- 画像フォルダ / ZIP / PDF 書籍の一覧表示
- サムネイル自動生成（ZIP は先頭画像、PDF は 1 ページ目）
- 表示モード切替
  - **棚モード**: 階層をたどって閲覧
  - **フラットモード**: 配下を再帰的に一覧化
- ★評価（お気に入り）管理
- タグ抽出・検索・フィルタリング
- 最近追加 / 未読 / 重複候補の確認
- 外部ビューア（例: Honeyview）連携

## 動作環境

- Python 3.10 以上（3.11 推奨）
- Windows を主対象（macOS / Linux でも Python + GUI 環境が整えば動作可能）

## セットアップ

```bash
git clone <this-repo-url>
cd Bookshelf
python -m venv .venv
```

仮想環境の有効化:

```bash
# Windows
.venv\Scripts\activate

# macOS / Linux
source .venv/bin/activate
```

依存関係のインストール:

```bash
pip install -r requirements.txt
```

## 起動方法

```bash
python Bookshelf_share.py
```

起動後の基本操作:

1. 書籍ルートフォルダを選択
2. `Scan` でライブラリを取り込み
3. 検索欄・★フィルタ・タグフィルタで絞り込み

## 設定（任意）

`Bookshelf_share.py` の先頭付近にある設定値を必要に応じて変更できます。

- `DATA_DIR`: DB / キャッシュ保存先（既定: `./data`）
- `VIEWER_EXE`: 外部ビューア実行ファイルのフルパス
- `MEMO_FILE_PATH`: メモファイルパス

## データ保存先

初回実行時に `data/` が作成され、以下が保存されます。

- `data/library.sqlite3` : 書籍メタデータ
- `data/thumbs/` : 生成済みサムネイル

## 依存ライブラリ

- PyQt6
- Pillow
- PyMuPDF

（加えて標準ライブラリの `sqlite3`, `zipfile`, `threading` などを利用）

## ライセンス

MIT License（`LICENSE` を参照）
