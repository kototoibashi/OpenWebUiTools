# Open WebUI Tools

Open WebUI で使うカスタム Tool を管理するリポジトリです。現在は HTTP URL の取得・本文抽出を行う Tool を収録しています。機能ごとに `tools/` 配下へ分類し、Tool ごとに独立して配布・導入できる構成にしています。

## 収録ツール

| 分類 | Tool | 概要 | ファイル |
| --- | --- | --- | --- |
| HTTP | HTTP Fetch | Web ページやテキスト URL を取得し、本文・見出し一覧・chunk・検索結果を返す | [`tools/http/http_fetch.py`](tools/http/http_fetch.py) |

### HTTP Fetch

Open WebUI のチャットから `fetch_url` を呼び出します。最初は URL だけを指定し、続きが必要な場合は `chunk`、本文内を探す場合は `query` を指定します。

- `url`: 取得する `http://` または `https://` URL
- `chunk`: 例 `c3`、`c3-c6`
- `query`: キャッシュした本文から探す語句
- `mode`: `extract` (既定)、`outline`、`raw`、`all`
- `refresh`: キャッシュを使わず再取得する

Tool は SSRF 対策として、既定で loopback / private IP 宛てのアクセスを拒否します。`ALLOW_PRIVATE_HOSTS` Valve は用途を確認して設定してください。
DNS 解決後は検査した IP に接続先を固定し、DNS 再解決による検査回避を防ぎます。この保護では環境変数などで設定した HTTP プロキシを使えない場合、取得をエラーにします。外部サイトへは Open WebUI 実行環境から直接接続できる必要があります。

## 導入

1. `tools/http/http_fetch.py` の内容を Open WebUI の **Workspace → Tools** で新しい Tool に貼り付けます。
2. `requirements` の依存関係を Open WebUI の Tool 設定に追加します: `requests`, `beautifulsoup4`。
3. Tool を保存し、利用するモデルに有効化します。

Open WebUI のバージョンやデプロイ方法によって依存パッケージの追加方法が異なるため、requirements の入力先は管理環境に合わせてください。

## リポジトリ構成

```text
.
├── tools/
│   └── http/                 # HTTP 系 Tools
├── docs/
│   └── notes/                # 設計・調査メモ
├── README.md
└── .gitignore
```

## Tool の追加方針

- 各 Tool は Open WebUI に貼り付けて使える、自己完結した Python ファイルとして `tools/<category>/` に置きます。
- 新しい連携先やプロトコルは適切な分類 (`search/`, `filesystem/`, `database/` など) の下に追加し、既存 Tool と依存関係や設定を混ぜません。
- 各 Tool の先頭に Open WebUI が読む `title`、`author`、`description`、`requirements` を記載します。
- 収録ツール表と使い方をこの README に更新します。複数 Tool を追加したら、分類ディレクトリごとに短い README を置くことも検討します。
- 調査・設計メモは `docs/notes/` に置き、利用者向けの導入手順とは分けます。

## 開発メモ

HTTP Fetch の HTML 抽出について確認した課題と改善案は [`docs/notes/http-fetch-review.txt`](docs/notes/http-fetch-review.txt) に保存しています。これは調査メモであり、現在の実装仕様を保証する文書ではありません。
