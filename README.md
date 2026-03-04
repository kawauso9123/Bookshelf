📚 Bookshelf

サムネイル一覧表示型のシンプルな本棚ビューアです。
フォルダ管理・外部ビューア連携・DBキャッシュ機能を備えています。

主な機能

📁 フォルダ単位の一覧表示

🖼 サムネイル表示（画像 / ZIP / PDF）

⭐ お気に入り管理

🗃 SQLite によるサムネイル保存

🚀 外部ビューア起動（ソース内指定）

🧭 フラット表示 / フォルダ表示切替

対応形式

画像（jpg / png 等）

ZIP（先頭画像を使用）

PDF（1ページ目を使用）

動作環境

Python 3.10 以上

Windows想定

必要ライブラリ
pip install PyQt6 Pillow PyMuPDF

環境構築（推奨）
```bash
./create_environment.sh
```

`.venv` に仮想環境が作成され、依存関係がインストールされます。

起動方法
python Bookshelf_share.py
外部ビューア設定

ソース内の以下を編集してください。

VIEWER_EXE = r"ビューアのフルパス"

未設定の場合は外部起動は無効です。

データ保存

実行時に data/ フォルダが自動生成されます。

thumbnails.db

キャッシュ画像

ライセンス
✅ MIT License
