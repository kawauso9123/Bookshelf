# 📚 Bookshelf

ローカル/NAS上の自炊書籍（画像フォルダ・ZIP・PDF）を、サムネイル付きで管理・閲覧するための PyQt6 製デスクトップ本棚アプリです。SQLite を使ったメタデータ管理により、検索・絞り込み・お気に入り管理を高速に行えます。

## 概要

- 画像フォルダ / ZIP / PDF の書籍を一覧表示
- サムネイルを自動生成（ZIP は先頭画像、PDF は1ページ目）
- ルート配下を「棚モード（階層表示）」と「フラットモード（再帰一覧）」で切り替え
- ★評価（お気に入り）やタグ抽出、最近追加・未読・重複候補の確認
- 外部ビューア（例: Honeyview）連携
- DB（`data/library.sqlite3`）とサムネイルキャッシュ（`data/thumbs`）をローカル保存

## インストール方法

### 1. Python を用意

- Python 3.10 以上を推奨
- Windows 環境を想定

### 2. リポジトリを取得

```bash
git clone <this-repo-url>
cd Bookshelf
```

### 3. 仮想環境を作成（任意だが推奨）

```bash
python -m venv .venv
# Windows
.venv\Scripts\activate
# macOS / Linux
source .venv/bin/activate
```

### 4. 依存パッケージをインストール

```bash
pip install -r requirements.txt
```

## 依存関係

`requirements.txt` に記載の主要依存関係:

- PyQt6
- Pillow
- PyMuPDF

標準ライブラリとして `sqlite3`, `zipfile`, `threading` などを利用しています。

## 使用方法

### 1. 初期設定（任意）

`Bookshelf_share.py` 先頭の設定値を必要に応じて編集します。

- `DATA_DIR`: DB/キャッシュ保存先（デフォルトは `./data`）
- `VIEWER_EXE`: 外部ビューア実行ファイルのフルパス
- `MEMO_FILE_PATH`: メモファイルのパス

### 2. アプリ起動

```bash
python Bookshelf_share.py
```

### 3. ルートフォルダを選択してスキャン

- 起動後に書籍のルートフォルダを選択
- `Scan` 実行で DB に書籍情報を登録
- 検索欄・★フィルタ・タグフィルタで絞り込み

## 実行例

```bash
$ python Bookshelf_share.py
# GUIが起動
# 例: D:\Comics をルートに選択して Scan
# -> ZIP/PDF/画像フォルダがカード表示され、サムネイルが順次生成される
# -> ★評価や検索ワードで一覧を絞り込める
```

## データ保存先

初回実行時に `data/` が作成され、以下が保存されます。

- `data/library.sqlite3` : 書籍メタデータ
- `data/thumbs/` : 生成済みサムネイル

## ライセンス

MIT License
