
"""
title: HTTP Fetch (Extract -> Outline -> Chunk)
author: custom
description: URLから本文とリンクID付きアウトラインを返す。リンクは同じ元URLとlink_idでたどり、続きはchunk/queryで取得する。キャッシュにより同じURLの再取得を避ける。text/markdown・.md/.txt/.rst・JSONなどに対応。
requirements: requests, beautifulsoup4
"""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import ipaddress
import json
import re
import socket
import time
import zlib
from bisect import bisect_right
from collections import OrderedDict
from typing import Any, Dict, List, Optional, Sequence, Tuple
from urllib.parse import urljoin, urlsplit, urlunsplit

import requests
from requests.adapters import HTTPAdapter, select_proxy
from requests.structures import CaseInsensitiveDict
from bs4 import BeautifulSoup, Comment
from pydantic import BaseModel, Field
from urllib3.connection import HTTPConnection as _U3HTTPConnection
from urllib3.connection import HTTPSConnection as _U3HTTPSConnection
from urllib3.connectionpool import HTTPConnectionPool as _U3HTTPConnectionPool
from urllib3.connectionpool import HTTPSConnectionPool as _U3HTTPSConnectionPool
from urllib3.exceptions import ConnectTimeoutError as _U3ConnectTimeoutError
from urllib3.exceptions import NewConnectionError as _U3NewConnectionError
from urllib3.util.connection import create_connection as _u3_create_connection

# lxml があれば使い、無ければ標準パーサに落ちる(requirements に lxml を足すと速くなる)
_BS_PARSER = "html.parser" if importlib.util.find_spec("lxml") is None else "lxml"

# Open WebUI はチャット/リクエスト単位で Tools を再生成し得るので、キャッシュはモジュールレベルに置く
_CACHE: "OrderedDict[str, Dict[str, Any]]" = OrderedDict()
_EXTRACTOR_VERSION = "5"

_ALWAYS_STRIP = ["script", "style", "noscript", "template", "svg", "math", "iframe",
                 "form", "button", "input", "select", "textarea", "link", "meta"]
_NOISE_STRIP = ["nav", "header", "footer", "aside", "[role=navigation]",
                "[role=banner]", "[role=contentinfo]", ".sidebar", ".menu",
                ".toc", ".table-of-contents", ".breadcrumb", ".tabs",
                ".tablist", "[aria-label*=nav]", "#footer", ".site-footer",
                ".footer-nav", ".footer-menu", ".global-nav", ".globalNav",
                "#global-nav", "#globalNav", ".skip-link", ".skip-to-content",
                ".skip-navigation", "[class*=skip-link]", "[id*=skip-link]",
                ".modal-close", ".close-button", "[aria-label=close]", "[aria-label=閉じる]"]
_CONTAINERS = ["article", "main", "[role=main]", ".markdown-body", "#readme",
               "#main-content", ".main-content", "#content", ".content",
               ".post-content", ".article-content", "#article-body", "#article",
               ".post", ".article", "body"]
_SELECTABLE = ["h1", "h2", "h3", "h4", "h5", "h6", "p", "pre", "table",
               "ul", "ol", "dl", "blockquote", "figure"]
_NESTED_SKIP = ["ul", "ol", "dl", "li", "table", "pre", "blockquote", "figure"]

_ASCII_ONLY = ("", "iso-8859-1", "latin-1", "latin1", "us-ascii", "windows-1252")
_CJK = re.compile(r"[\u3040-\u30ff\u3400-\u4dbf\u4e00-\u9fff\uac00-\ud7af\uff00-\uffef]")
_WS = re.compile(r"[ \t\r\f\v]+")
_META_CHARSET = re.compile(rb'<meta[^>]+charset=["\']?([A-Za-z0-9_\-]+)', re.I)
_HEADER_CHARSET = re.compile(r"charset=([\w\-]+)", re.I)
_URL_RE = re.compile(r"https?://[^\s<>\"')\]]+", re.I)
_MAP_LINK_HOSTS = (
    "geohack.toolforge.org", "osm4wiki.toolforge.org", "maps.google.com",
    "google.com", "bing.com", "mapfan.com", "mapion.co.jp", "map.yahoo.co.jp",
    "navitime.co.jp", "zenrin.co.jp",
)

# Markdown / テキスト系(拡張子・magic による fallback 用)
_MD_HEAD_EXT = (".md", ".markdown", ".rst")
_MD_ANY_EXT = _MD_HEAD_EXT + (".txt", ".text")
_TEXTY_EXT = _MD_ANY_EXT + (".log",)
_MD_BINARY_EXT = (".pdf", ".png", ".jpg", ".jpeg", ".gif", ".webp", ".ico", ".zip", ".gz", ".tgz",
                  ".bz2", ".xz", ".7z", ".rar", ".mp3", ".mp4", ".m4a", ".mov", ".avi", ".mkv",
                  ".woff", ".woff2", ".ttf", ".otf", ".exe", ".bin", ".so", ".dll", ".class", ".jar",
                  ".wasm", ".parquet", ".iso", ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx",
                  ".dmg", ".apk", ".epub", ".cab", ".deb", ".rpm")
_BIN_MAGIC = (b"%PDF", b"PK\x03\x04", b"PK\x05\x06", b"PK\x07\x08", b"\x1f\x8b", b"\x1f\xa0",
              b"BZh", b"\xfd7zXZ\x00", b"7z\xbc\xaf\x27\x1c", b"Rar!\x1a\x07", b"\x89PNG",
              b"\xff\xd8\xff", b"GIF8", b"\x7fELF", b"\xca\xfe\xba\xbe", b"CAFEBABE", b"ID3",
              b"OggS", b"SQLite format 3", b"PAR1", b"bplist00", b"\x00\x00\x01\x00",
              b"\x00\x00\x02\x00", b"\xc2\xb5FOR\x02", b"\x1aE\xdf\xa3", b"\x00\x00\x00ftyp")
_OCTETISH_CT = ("octet", "pdf", "image/", "video/", "audio/", "font/", "zip", "gzip", "compress",
                "x-tar", "protobuf", "grpc", "parquet", "msword", "excel", "powerpoint",
                "opendocument", "vnd.android.package")
_MD_CT_KEYS = ("markdown", "x-md", "text/md", "+md")
_TEXT_CT_KEYS = ("plain", "csv", "javascript", "x-sh", "x-web", "x-python", "x-diff", "x-log",
                 "asciidoc")
_MODES = ("extract", "outline", "raw", "all", "full")
_NEGATIVE_STATUSES = {403, 404, 410, 429, 451, 500, 502, 503, 504}


# ---------------------------------------------------------------- helpers

def _norm(s: str) -> str:
    s = re.sub(r"[\u200b\u200c\u200d\ufeff\u00ad]", "", s)
    s = s.replace("\r", "\n").replace("\u00a0", " ")
    s = _WS.sub(" ", s)
    s = re.sub(r" ?\n ?", "\n", s)
    s = re.sub(r"\n{3,}", "\n\n", s)
    return s.strip()


def _est_tokens(s: str) -> int:
    n = len(s)
    if n == 0:
        return 0
    cjk = len(_CJK.findall(s))
    return int(cjk / 1.7 + (n - cjk) / 4) + 1


def _kfmt(n: int) -> str:
    return "{:,}".format(n) if n < 10000 else "{:.1f}k".format(n / 1000.0)


def _canonical(url: str) -> Optional[str]:
    """Cache key 専用の正規化。末尾スラッシュを変えるため送信URLには使わない。"""
    url = (url or "").strip()
    if not url:
        return None
    if "://" not in url:
        url = "https://" + url
    p = urlsplit(url)
    if p.scheme not in ("http", "https") or not p.netloc:
        return None
    path = re.sub(r"/{2,}", "/", p.path or "/")
    if path != "/" and path.endswith("/"):
        path = path[:-1]
    return urlunsplit((p.scheme.lower(), p.netloc.lower(), path, p.query, ""))


def _toggle_trailing_slash(url: str) -> Optional[str]:
    """Return the same HTTP URL with its non-root path slash toggled."""
    try:
        p = urlsplit(url)
    except ValueError:
        return None
    if p.scheme not in ("http", "https") or not p.netloc or not p.path or p.path == "/":
        return None
    path = p.path[:-1] if p.path.endswith("/") else p.path + "/"
    return urlunsplit((p.scheme, p.netloc, path, p.query, p.fragment))


def _normalize_host(host: str) -> str:
    """数値だけで書かれた host を点結み IPv4 に正規化する。ip_address() だけでは ValueError で
    検査を素通りするが、requests/urllib3 は inet_aton 相当(127.1 / 0x7f000001 / 2130706433 /
    0177.0.0.1)で解釈する。検査側を実接続側と同じ基準に揃える。"""
    h = (host or "").strip()
    if h.startswith("[") and h.endswith("]"):
        h = h[1:-1]
    if not h:
        return ""
    parts = h.split(".")
    if parts and all(re.fullmatch(r"0[xX][0-9a-fA-F]+|0[0-7]+|[0-9]+", p) for p in parts):
        try:
            return socket.inet_ntoa(socket.inet_aton(h))
        except OSError:
            pass
        try:
            return str(ipaddress.ip_address(h))
        except ValueError:
            return h
    return h


# Python の is_private / is_reserved が拾わんが、SSRF 実用上塞ぎたい範囲(実測で素通り確認済み)
_EXTRA_NETS = [
    ("100.64.0.0/10", "CGNAT(キャリアグレードNAT)"),
    ("192.88.99.0/24", "6to4 リレー anycast(旧割当)"),
    ("192.0.0.0/24", "IETF プロトコル割当"),
    ("198.18.0.0/15", "機器ベンチマーク試験用"),
    ("100::/64", "IPv6 discard-only"),
]


def _extra_block(ip) -> str:
    for cidr, label in _EXTRA_NETS:
        try:
            if ip in ipaddress.ip_network(cidr):
                return label
        except ValueError:
            continue
    return ""


def _normalize_allow_private(val: Any) -> str:
    """ALLOW_PRIVATE_HOSTS を off / self_only / all の 3 値に寄せる(後方互換で bool も受け取る)。"""
    if isinstance(val, bool):
        return "all" if val else "off"
    s = str(val or "").strip().lower()
    if s in ("", "off", "false", "0", "no", "none"):
        return "off"
    if s in ("self", "self_only", "private", "lan", "on", "true", "1", "yes"):
        return "self_only"
    if s in ("all", "any"):
        return "all"
    return "off"


def _checked_addresses(url: str, allow_private: Any) -> Tuple[List[str], str]:
    """SSRF防止。host を正規化してから解決後の IP で私有/ループバック等を拒否する。
    検査したアドレスも返し、HTTP transport がその IP に直接接続する。
    段階(実測で 169.254 / CGNAT の扱いが変わる):
      off       私有/ループバック/link-local/multicast/unspecified/追加範囲を全部ブロック
      self_only loopback と私有LANは許可。link-local(クラウドメタデータ)・unspecified・
                multicast・CGNAT系は許可設定に関係なくブロック(自己ホスト運用は保つ)
      all       宛先IPの範囲検査だけ緩める(scheme と host 妥当性は引き続き検査する)"""
    mode = _normalize_allow_private(allow_private)
    try:
        p = urlsplit(url)
    except ValueError:
        return [], "Unable to parse URL host."
    host = _normalize_host(p.hostname or "")
    if not host:
        return [], "Unable to parse URL host."
    try:
        port = p.port or (443 if p.scheme == "https" else 80)
    except ValueError:
        return [], "Unable to parse URL port."
    addrs: List[str] = []
    try:                                  # IP リテラルは DNS を経ずに検査できる
        addrs = [str(ipaddress.ip_address(host))]
    except ValueError:
        try:
            infos = socket.getaddrinfo(host, port)
        except socket.gaierror:
            return [], "DNS resolution failed: " + host
        addrs = list(dict.fromkeys(str(i[4][0]) for i in infos))
    if not addrs:
        return [], "DNS resolution returned no usable addresses: " + host
    for addr in addrs:
        try:
            ip = ipaddress.ip_address(addr.split("%", 1)[0])
        except ValueError:
            continue
        why = ""
        always = (ip.is_link_local or ip.is_unspecified or ip.is_multicast)
        if always and mode != "all":
            why = "link-local/unspecified/multicast (blocked even when private hosts are allowed)"
        if not why:
            why = _extra_block(ip)
        if not why and mode == "off":
            mapped = getattr(ip, "ipv4_mapped", None)
            bad = (ip.is_private or ip.is_loopback or ip.is_link_local or ip.is_reserved
                   or ip.is_multicast or ip.is_unspecified
                   or (mapped is not None and (mapped.is_private or mapped.is_loopback)))
            if bad:
                why = "private/loopback IP"
        if why:
            return [], "Blocked for security: " + host + " -> " + addr + " (" + why + ")"
    return addrs, ""


def _blocked_host(url: str, allow_private: Any) -> str:
    """Compatibility wrapper for callers that only need the rejection reason."""
    _, error = _checked_addresses(url, allow_private)
    return error


class _PinnedHTTPConnection(_U3HTTPConnection):
    """HTTP connection that never performs DNS after destination validation."""
    def __init__(self, *args, pinned_ip: str, **kwargs):
        self._pinned_ip = pinned_ip
        super().__init__(*args, **kwargs)

    def _new_conn(self):
        try:
            return _u3_create_connection((self._pinned_ip, self.port), self.timeout,
                                         source_address=self.source_address,
                                         socket_options=self.socket_options)
        except socket.timeout as e:
            raise _U3ConnectTimeoutError(
                self, "Connection to pinned IP " + self._pinned_ip + " timed out") from e
        except OSError as e:
            raise _U3NewConnectionError(
                self, "Failed to connect to pinned IP " + self._pinned_ip + ": " + str(e)) from e


class _PinnedHTTPSConnection(_U3HTTPSConnection):
    """HTTPS variant: socket goes to pinned_ip while TLS still uses the URL host."""
    def __init__(self, *args, pinned_ip: str, **kwargs):
        self._pinned_ip = pinned_ip
        super().__init__(*args, **kwargs)

    def _new_conn(self):
        try:
            return _u3_create_connection((self._pinned_ip, self.port), self.timeout,
                                         source_address=self.source_address,
                                         socket_options=self.socket_options)
        except socket.timeout as e:
            raise _U3ConnectTimeoutError(
                self, "Connection to pinned IP " + self._pinned_ip + " timed out") from e
        except OSError as e:
            raise _U3NewConnectionError(
                self, "Failed to connect to pinned IP " + self._pinned_ip + ": " + str(e)) from e


class _PinnedHTTPPool(_U3HTTPConnectionPool):
    ConnectionCls = _PinnedHTTPConnection


class _PinnedHTTPSPool(_U3HTTPSConnectionPool):
    ConnectionCls = _PinnedHTTPSConnection


class _PinnedIPAdapter(HTTPAdapter):
    """Requests adapter that connects to a previously checked IP, preserving URL host/TLS."""
    def __init__(self, pinned_ip: str):
        self.pinned_ip = pinned_ip
        super().__init__(max_retries=0)

    def _pool_for(self, scheme: str, host: str, port: Optional[int], pool_kwargs=None):
        if scheme not in ("http", "https") or not host:
            raise requests.exceptions.InvalidURL("Only http/https URLs with a host are allowed")
        kwargs = dict(pool_kwargs or {})
        kwargs["pinned_ip"] = self.pinned_ip
        if scheme == "https":
            # Keep certificate verification and SNI bound to the original hostname.
            kwargs["assert_hostname"] = host
            pool = _PinnedHTTPSPool
        else:
            pool = _PinnedHTTPPool
        return pool(host=host, port=port, **kwargs)

    def get_connection(self, url, proxies=None):
        if select_proxy(url, proxies):
            raise requests.exceptions.ProxyError(
                "HTTP proxy is incompatible with DNS-pinned SSRF protection")
        p = urlsplit(url)
        return self._pool_for(p.scheme, p.hostname or "", p.port)

    def get_connection_with_tls_context(self, request, verify, proxies=None, cert=None):
        if select_proxy(request.url, proxies):
            raise requests.exceptions.ProxyError(
                "HTTP proxy is incompatible with DNS-pinned SSRF protection")
        host_params, pool_kwargs = self.build_connection_pool_key_attributes(
            request, verify, cert)
        scheme = host_params.pop("scheme")
        return self._pool_for(scheme, host_params["host"], host_params.get("port"), pool_kwargs)


_REDIRECT_STATUSES = {301, 302, 303, 307, 308}


def _next_hop_url(current: str, loc: str) -> Tuple[str, str]:
    """Location を絶対URL化して scheme と host を検査する。私有IP等の宛先検査は _blocked_host がやる。
    userinfo(user:pass@host)・backslash・制御文字を含む Location は、検査に使う urlsplit と
    requests/urllib3 の実接続 host 解釈がずれ得るさかい、ここで段階的に弾く(実測で
    urlsplit.hostname と parse_url().host が食い違う形が存在する)。"""
    loc = (loc or "").strip()
    if not loc:
        return "", ""
    if any((ord(c) < 32) or ord(c) == 127 for c in loc):
        return "", "Blocked redirect: Location contains control characters."
    if any(c in "@\\" for c in loc):
        return "", "Blocked redirect: Location contains userinfo (@) or a backslash."
    try:
        nxt = urljoin(current, loc)
    except Exception as e:
        return "", "Unable to parse redirect URL: " + type(e).__name__ + ": " + str(e)
    s = urlsplit(nxt)
    if s.scheme not in ("http", "https"):
        return "", "Blocked redirect scheme: " + (s.scheme or "(none)") + " (only http/https are allowed)."
    if not s.hostname:
        return "", "Unable to parse redirect host: " + nxt
    if s.username or s.password:
        return "", "Blocked redirect: userinfo (user:pass@) is not allowed in Location."
    try:                                  # requests 実接続側の解釈と突き合わせる
        from urllib3.util import parse_url as _pu
        uh = _pu(nxt).host
    except Exception:
        uh = None
    if uh:
        a = _normalize_host(uh).lower()
        b = _normalize_host(s.hostname).lower()
        if a and b and a != b:
            return "", ("Blocked redirect: host parsing mismatch (urlsplit=" + str(s.hostname)
                        + " / urllib3=" + str(uh) + ").")
    return nxt, ""


def _cache_get(key: str, ttl: int) -> Tuple[Optional[Dict[str, Any]], int]:
    ent = _CACHE.get(key)
    if not ent:
        return None, 0
    limit = int(ent.get("ttl") or ttl)      # 失敗応答は個別の短めTTLで保持する
    age = int(time.time() - ent["fetched_at"])
    if age > limit:
        _CACHE.pop(key, None)
        return None, 0
    _CACHE.move_to_end(key)
    return ent, max(0, limit - age)


def _cache_set(key: str, ent: Dict[str, Any], max_entries: int) -> None:
    _CACHE[key] = ent
    _CACHE.move_to_end(key)
    while len(_CACHE) > max(1, max_entries):
        _CACHE.popitem(last=False)


def _cache_put(keys: Sequence[str], payload: Dict[str, Any], max_entries: int) -> None:
    for k in keys:
        if not k:
            continue
        _CACHE[k] = payload
        _CACHE.move_to_end(k)
    while len(_CACHE) > max(1, int(max_entries)):
        _CACHE.popitem(last=False)


# ---------------------------------------------------------------- decode

def _apparent_encoding(data: bytes) -> Optional[str]:
    """byte列から charset を推定する(requests の Response.apparent_encoding には依存せんとる)。

    requests.models.Response.apparent_encoding は中で self.content を読む。
    stream=True で iter_content を使い切った後の Response やと、
    content property が `self._content is False and self._content_consumed` を検知して
    RuntimeError("The content for this response was already consumed") を投げる
    (iter_content 側は StreamConsumedError。これは requests 上 RequestException と TypeError の両方)。
    RequestsException を握っとる except に化けて「取得失敗」に見えるから、
    レスポンスの推定APIには触んのが安全や。
    """
    try:
        from charset_normalizer import from_bytes
        best = from_bytes(data[:200_000]).best()
        if best is not None:
            return str(best.encoding)
    except Exception:
        pass
    try:
        import chardet
        enc = chardet.detect(data[:200_000]).get("encoding")
        if enc:
            return str(enc)
    except Exception:
        pass
    return None


def _decode(data: bytes, ct: str, headers, apparent: Optional[str]) -> Tuple[str, str]:
    """charset を ヘッダ -> meta sniffing -> utf-8 strict -> apparent の順で決める。
    国内サイトで多い 'ヘッダはISO-8859-1宣言だが中身はUTF-8/Shift_JIS' による文字化けを防ぐ。"""
    enc = ""
    apparent = apparent or _apparent_encoding(data)   # header 指定無しでも byte列から自力で推定
    m = _HEADER_CHARSET.search(ct or "")
    if m:
        enc = m.group(1)
    if not enc:
        enc = requests.utils.get_encoding_from_headers(headers) or ""
    declared = (enc or "").lower()

    if declared in _ASCII_ONLY:
        sm = _META_CHARSET.search(data[:4096])
        if sm:
            enc = sm.group(1).decode("ascii", "replace")
        else:
            try:
                data.decode("utf-8")
                enc = "utf-8"
            except UnicodeDecodeError:
                enc = apparent or "utf-8"

    try:
        text = data.decode(enc, "replace")
    except (LookupError, TypeError):
        return data.decode("utf-8", "replace"), "unknown-codec:" + enc
    except UnicodeDecodeError:
        text = data.decode("utf-8", "replace")

    if "\ufffd" in text[:4000]:
        for alt in ("utf-8", apparent, "shift_jis", "euc-jp", "cp932"):
            if not alt:
                continue
            try:
                text = data.decode(alt)
                enc = (declared or enc) + "->" + alt
                break
            except (LookupError, TypeError, UnicodeDecodeError):
                continue
    return text, enc
def _status_message(code: int, reason: str, url: str, hops: int, origin: str) -> str:
    # HTTP 4xx/5xx をステータス別に案内。現行版は 404/403/410/429/503/401 で同一文で、
    # 404 に refresh 案内、403 に末尾スラッシュ案内を乗せて LLM を無駄リトライへ誘導していた。
    reason = (reason or "").strip()
    head = "HTTP " + str(code) + ((" " + reason) if reason else "") + " (" + url + ")"
    tail = ""
    if hops:
        tail += " / Response after " + str(hops) + " redirect hop(s) (original URL: " + origin + ")"
    if code == 404:
        tail += (" / The page could not be retrieved. Retrying with mode, chunk, query, or refresh will not help."
                   " Check the spelling, path, and trailing slash. Try the site index (llms.txt, sitemap, or parent directory),"
                   " or the same page as .md or .txt.")
    elif code == 403:
        tail += (" / The URL may exist; access was denied. Retrying the same request will not retrieve its content."
                   " Repeated requests may worsen the block. Try another public URL or the same page as .md, .txt, or llms.txt.")
    elif code == 410:
        tail += " / This resource was permanently removed. Try the parent directory or site search."
    elif code == 429:
        tail += " / Rate limited. Wait before retrying or use another URL; refresh=true may make this worse."
    elif code in (401, 402, 407):
        tail += " / Authentication, payment, or proxy credentials are required. This tool does not store credentials; use a public URL."
    elif code == 451:
        tail += " / Access was denied for legal reasons. Retrying will not help."
    elif 400 <= code < 500:
        tail += " / The request was invalid. Check the URL and query parameters."
    elif 500 <= code < 600:
        tail += " / Server error. Wait a while, then retry once."
    else:
        tail += " / The response body could not be retrieved."
    return head + tail

def _ext_of(url: str) -> str:
    """URL path の末尾から拡張子(小文字)を拾う。/quick-start.md?raw=1 -> .md"""
    try:
        path = urlsplit(url).path or ""
    except Exception:
        path = url or ""
    seg = path.rstrip("/").rsplit("/", 1)[-1]
    dot = seg.rfind(".")
    if dot <= 0:
        return ""
    ext = seg[dot:].lower()
    return ext if 1 < len(ext) <= 6 and re.fullmatch(r"\.[a-z0-9]+", ext) else ""

def _is_binary_magic(data: bytes) -> str:
    """先頭の magic signature でバイナリを判定する(content-type 偽宣言より信頼できる)。"""
    for magic in _BIN_MAGIC:
        if data.startswith(magic):
            return "magic:" + repr(magic[:8])
    if b"\x00" in data[:4096]:
        return "magic: contains NUL byte"
    return ""


def _looks_text(data: bytes) -> Tuple[bool, str]:
    """テキストとみなしてよいか(制御文字の割合で判定)。
    \t \n \r \f \x1b は除外する。ch<9 or 10<ch<127 のような基準にすると LF(10) が
    不合格になって普通の ASCII 本文が 100% 弾かれる(実測で踏んだ坑)。"""
    if not data:
        return True, ""
    sample = data[:16384]
    if b"\x00" in sample:
        return False, "NUL byte detected"
    bad = 0
    for ch in sample:
        if ch in (9, 10, 13, 12, 27):
            continue
        if ch < 32 or ch == 127:
            bad += 1
    ratio = bad / max(1, len(sample))
    if ratio > 0.01:
        return False, ("Control character ratio " + format(ratio * 100.0, ".1f") + "%")
    return True, ""

def _classify(ct: str, data: bytes, url: str) -> Dict[str, Any]:
    #     コンテンツタイプ + 拡張子 + magic から分岐を決める。
    # content-type 単独だと raw.githubusercontent の text/plain 宣言 .md や octet-stream 宣言 .md
    # を取り逃す。want_headings は見出し group 化を適用するかなり(.log / shell 系の # 行を
    # 偽見出しにせんとるための制限)。
    ctl = (ct or "").lower()
    ext = _ext_of(url)
    head = data[:400].lstrip().lower()
    md_ct = any(k in ctl for k in _MD_CT_KEYS)
    html_ct = ("html" in ctl) or ("xml" in ctl)
    json_ct = "json" in ctl
    plain_ct = any(k in ctl for k in _TEXT_CT_KEYS)
    octet_ct = any(k in ctl for k in _OCTETISH_CT)
    looks_html = head.startswith((b"<!doctype html", b"<html", b"<?xml"))
    magic = _is_binary_magic(data)
    text_ok, why_not = _looks_text(data)
    is_html = bool((html_ct and not magic) or (not html_ct and not octet_ct and looks_html and text_ok))
    is_json = bool((json_ct and not magic)
                    or (not html_ct and not json_ct and not md_ct and not octet_ct
                        and head[:1] in (b"{", b"[") and text_ok))
    is_md = bool(md_ct and not magic)
    is_plain = bool((plain_ct and not magic)
                    or (not html_ct and not json_ct and not md_ct and not octet_ct and text_ok))
    note = ""
    rescued = False
    if not (is_html or is_json or is_md or is_plain):
        if octet_ct or (not ctl) or ctl.startswith(("application/", "binary/", "message/")):
            if ext in _MD_BINARY_EXT:
                note = ("Extension " + ext + " is a binary format; body extraction skipped (content-type: "
                        + (ct or "unknown") + ")")
            elif magic:
                note = "File signature is " + magic + "; body extraction skipped"
            elif ext in _TEXTY_EXT and text_ok:
                is_plain = True
                rescued = True
                note = "Content type %s is not text, but extension %s and file contents indicate text" % ((ct or "unknown"), ext)
    is_text = bool(is_html or is_json or is_md or is_plain)
    want_headings = bool(is_md or (is_plain and (ext in _MD_ANY_EXT)))
    skip_reason = note or (("Not text: " + why_not) if why_not
                           else "Unsupported content type for text extraction")
    return {"ct": ctl, "ext": ext, "is_html": is_html, "is_json": is_json, "is_md": is_md,
            "is_plain": is_plain, "is_text": is_text, "want_headings": want_headings,
            "octet_ct": octet_ct, "magic": magic, "rescued": rescued,
            "skip_reason": skip_reason, "not_text_reason": why_not, "note": note}

def _md_groups(text: str) -> List[Dict[str, Any]]:
    # Markdown / Markdown転写 text/plain を見出し単位 group 化。地雷4つの扱い:
    #  1) コードフェンス内の # は見出しにせんの(fence 状態管理)
    #  2) ATX は前後空行(flanking)を要求(文中の inline # を救わん)
    #  3) YAML frontmatter は剥ぐ(--- だけの junk chunk を出さん)
    #  4) setext は = (H1)だけ拾う。- は HR(水平線)と区別できんさかい本文に残す
    #     (docs 実データは ATX 中心で、- を見出しにすると本文が細切れ化するため正直な妥協)
    BT = '```'; TIL = '~~~'
    lines = text.replace(chr(13)+chr(10), chr(10)).replace(chr(13), chr(10)).split(chr(10))
    n = len(lines)
    i = 0
    while i < n and not lines[i].strip():
        i += 1
    if i < n and lines[i].strip() in ("---", "..."):
        for j in range(i + 1, min(n, i + 80)):
            if lines[j].strip() in ("---", "..."):
                i = j + 1
                break
    groups = []
    cur = None
    fence = ""

    def open_group(title=None, level=None):
        g = {"title": title, "level": level, "lines": [], "flags": set()}
        groups.append(g)
        return g

    def add_line(line, flag=""):
        nonlocal cur
        if cur is None:
            cur = open_group(None, None)
        cur["lines"].append(line)
        if flag:
            cur["flags"].add(flag)

    def blank_before(idx):
        return idx == i or (idx > 0 and not lines[idx - 1].strip())

    for idx in range(i, n):
        raw = lines[idx]
        s = raw.strip()
        if fence:
            add_line(raw, "code")
            if s and len(s) >= 3 and set(s) <= set(fence):
                fence = ""
            continue
        if s[:3] in (BT, TIL):
            fence = s[:3]
            add_line(raw, "code")
            continue
        if s.startswith("#"):
            hashes = 0
            while hashes < len(s) and s[hashes] == "#":
                hashes += 1
            rest = s[hashes:]
            if 1 <= hashes <= 6 and rest.startswith(" ") and rest.strip() and blank_before(idx):
                body = rest.rstrip()
                k = len(body)
                while k > 0 and body[k - 1] == "#":
                    k -= 1
                if 0 < k < len(body) and body[k - 1] in (" ", chr(9)):
                    body = body[:k]
                cur = open_group(body.strip(), hashes)
                continue
            add_line(raw)
            continue
        if s and idx + 1 < n and blank_before(idx):
            nxt = lines[idx + 1].strip()
            if nxt and len(set(nxt)) == 1 and nxt[0] == "=" and len(nxt) >= 2:
                cur = open_group(s, 1)
                lines[idx + 1] = ""
                continue
        add_line(raw)

    out = []
    for g in groups:
        body = list(g["lines"])
        while body and not body[0].strip():
            body.pop(0)
        while body and not body[-1].strip():
            body.pop()
        if not body:
            if g["title"] and out:
                out[-1]["lines"].append("#" * int(g["level"] or 2) + " " + g["title"])
            elif g["title"]:
                out.append({"title": g["title"], "level": g["level"],
                                  "lines": ["# " + g["title"]], "flags": set()})
            continue
        flags = set(g["flags"])
        if BT in chr(10).join(body):
            flags.add("code")
        out.append({"title": g["title"], "level": g["level"], "lines": body, "flags": flags})
    return out
# ---------------------------------------------------------------- download

def _download(url: str, v) -> Tuple[Optional[Dict[str, Any]], str, Dict[str, Any]]:
    headers = {
        "User-Agent": v.USER_AGENT,
        "Accept": "text/html,application/xhtml+xml,application/json;q=0.9,text/plain;q=0.8,*/*;q=0.5",
        "Accept-Language": "ja,en;q=0.8",
    }
    sess = requests.Session()
    # SSRF: disable automatic redirects and validate every hop. Each hop's
    # checked IP is pinned by the transport adapter, so requests cannot resolve
    # the hostname again and land on a private address after validation.
    # Proxies are rejected by the adapter because they would resolve the origin
    # outside this process and bypass the pinned destination.
    max_hops = max(0, int(v.MAX_REDIRECTS))
    allow_private = _normalize_allow_private(getattr(v, "ALLOW_PRIVATE_HOSTS", "off"))   # bool valve 名はそのまま値だけ 3 値化
    current = (url or "").strip()          # 渡されたURLをそのまま送る(canon は cache key 専用)
    pinned_adapter = _PinnedIPAdapter("0.0.0.0")
    sess.mount("http://", pinned_adapter)
    sess.mount("https://", pinned_adapter)
    r = None
    hops = 0
    while True:
        addresses, blocked = _checked_addresses(current, allow_private)
        if blocked:
            if hops == 0:
                return None, blocked, {"url": current}
            return None, blocked + " (redirect target, hop " + str(hops) + ")", {"url": current}
        # Pin the socket destination to the exact address set that passed checks.
        # The request URL remains unchanged for Host routing and TLS verification.
        pinned_adapter.pinned_ip = addresses[0]
        try:
            r = sess.get(current, timeout=v.TIMEOUT, headers=headers, stream=True,
                         allow_redirects=False)             # ★ 自前で追う
        except requests.exceptions.RequestException as e:
            return None, "HTTP Request Error: " + type(e).__name__ + ": " + str(e), {}

        loc3 = (r.headers.get("location") or "").strip()
        if r.status_code in _REDIRECT_STATUSES and hops < max_hops and loc3:
            nxt, err = _next_hop_url(current, loc3)
            try:
                r.close()                                    # 3xx の本文は読まない・捨てて良い
            except Exception:
                pass
            if err:
                return None, err, {"url": current, "status": r.status_code}
            try:
                sess.cookies.clear()   # hop を跨いで Cookie が外部->内部へ移動する筋を塞ぐ
            except Exception:
                pass
            hops += 1
            current = nxt
            continue
        break

    if r is None:
        return None, "Redirect follow failed.", {}

    if r.status_code in _REDIRECT_STATUSES:
        # ここまで届いた 3xx = 追従しなかった(上限到達 / MAX_REDIRECTS=0 / Location 無し / 最終hopが3xx)
        loc = (r.headers.get("location") or "").strip()
        try:
            r.close()
        except Exception:
            pass
        if not loc:
            msg = ("HTTP " + str(r.status_code) + " redirect without a Location header: " + r.url
                   + " / This redirect response has no body; automatic redirects are disabled.")
        elif max_hops:
            msg = ("HTTP " + str(r.status_code) + " redirect limit reached: " + r.url
                   + " / MAX_REDIRECTS=" + str(max_hops))
        else:
            msg = ("HTTP " + str(r.status_code) + " redirect: " + r.url
                   + " / Not followed because MAX_REDIRECTS=0")
        if loc:
            msg += " / Location: " + loc[:300]
        msg += " / Retrying with mode or refresh will not help. Use the Location URL directly."
        return None, msg, {"url": r.url, "status": r.status_code}

    meta = {"url": r.url, "status": r.status_code, "ct": (r.headers.get("content-type") or "").strip(),
            "hops": hops}
    if hops:
        meta["redirected_from"] = (url or "").strip()
    final = _canonical(r.url if isinstance(r.url, str) else "")   # cache alias (meta ni deru saishu URL demo heru)
    if final:
        meta["final"] = final
    # ★ iter_content を消費して close した後は、r.text / r.content / r.apparent_encoding / r.raw を
    #    绝对に触れんこと。StreamConsumedError(兼 RuntimeError)で落ちる。
    #    charset 判定に要る header だけ先にコピーする。
    #    注意: dict(r.headers) にすると CaseInsensitiveDict の性質が飛んで、
    #    requests.utils.get_encoding_from_headers() が "Content-Type" を見失い
    #    charset 宣言を無視する(= 文字化けの元)。CaseInsensitiveDict のまま保つ。
    try:
        headers_snapshot = CaseInsensitiveDict(r.headers)
    except Exception:
        headers_snapshot = r.headers

    data = b""
    total = 0
    truncated = False
    try:
        limit = max(50_000, int(v.MAX_DOWNLOAD_KB) * 1024)
        parts: List[bytes] = []
        for part in r.iter_content(chunk_size=65536):   # 受信途中で打ち切る(大きいレスポンス対策)
            if not part:
                continue
            parts.append(part)
            total += len(part)
            if total >= limit:
                truncated = True
                break
        data = b"".join(parts)
    except requests.exceptions.RequestException as e:
        # iter_content は ChunkedEncodingError / ContentDecodingError / ConnectionError を投げる
        return None, "HTTP request error while receiving data: " + type(e).__name__ + ": " + str(e), meta
    except Exception as e:
        return None, "Unexpected error while receiving data: " + type(e).__name__ + ": " + str(e), meta
    finally:
        r.close()

    meta["bytes"] = total
    meta["truncated"] = truncated

    if r.status_code == 403:
        server = (headers_snapshot.get("server") or "").lower()
        body_start = data[:20000].decode("utf-8", "ignore").lower()
        cf_challenge = (("cloudflare" in server or headers_snapshot.get("cf-mitigated", "").lower() == "challenge")
                        and ("just a moment" in body_start or "challenge-platform" in body_start
                             or headers_snapshot.get("cf-mitigated", "").lower() == "challenge"))
        if cf_challenge:
            return None, ("HTTP 403 Cloudflare browser challenge (" + r.url + ") / The server returned a JavaScript verification page, not the article. "
                          "This fetcher does not run the challenge or reuse browser cookies. Retrying the same URL will not help; "
                          "use an accessible mirror or provide the page text directly."), meta

    if r.status_code >= 400:
        reason = getattr(r, "reason", "") or ""
        return None, _status_message(r.status_code, reason, r.url, hops, (url or "").strip()), meta

    cls = _classify(meta["ct"], data, r.url)
    is_html = cls["is_html"]
    is_json = cls["is_json"]
    is_text = cls["is_text"]
    meta["ext"] = cls["ext"]
    if cls["rescued"]:
        meta["ct_fallback"] = True

    if total == 0 or r.status_code == 204 or r.status_code == 304:
        if r.status_code == 304:
            note = ("HTTP 304 Not Modified: no If-None-Match / If-Modified-Since header was sent. "
                    "An upstream CDN or proxy cache may be involved; try adding a cache-busting query such as ?cb=1.")
        elif r.status_code == 204:
            note = "HTTP 204 No Content: the server intentionally returned no body."
        else:
            note = "HTTP 200 returned an empty body (0 bytes)."
        return None, note + " The URL may still be valid; try another URL instead of retrying with mode or refresh.", meta

    if not is_text:
        meta["meta_only"] = True
        why = cls["skip_reason"] or ("content-type: " + (meta["ct"] or "unknown"))
        entry = {"meta": meta, "fetched_at": time.time(), "extractor_version": _EXTRACTOR_VERSION,
                 "title": "", "text": "",
                 "chunks": [], "total_chars": 0, "total_tokens": 0, "removed": 0, "raw": None,
                 "notes": ["Body extraction is unsupported: " + why + " (received " + _kfmt(total) + " bytes)",
                           "PDF, images, and archives are not extracted; chunk and query are unavailable for this URL.",
                           "Documentation sites may offer the same page as .md, .txt, or llms.txt."]}
        entry["snapshot"] = hashlib.sha256(
            (str(entry["fetched_at"]) + (meta.get("final") or url) + _EXTRACTOR_VERSION).encode()).hexdigest()[:12]
        return entry, "", meta

    text, charset = _decode(data, meta["ct"], headers_snapshot, None)
    meta["charset"] = charset
    meta["is_html"] = is_html

    entry = {"meta": meta, "fetched_at": time.time(), "extractor_version": _EXTRACTOR_VERSION, "notes": []}
    entry["snapshot"] = hashlib.sha256(
        (str(entry["fetched_at"]) + (meta.get("final") or url) + _EXTRACTOR_VERSION).encode()).hexdigest()[:12]
    raw_cap = 600_000
    entry["raw"] = zlib.compress(data[:raw_cap], 6)
    entry["raw_bytes"] = total
    if cls["note"]:
        entry["notes"].append(cls["note"])

    if is_html:
        ex = _extract_html(text, meta.get("final") or url)
        entry["title"] = ex["title"]
        entry["removed"] = ex["removed"]
        entry["compacted"] = ex.get("compacted", 0)
        entry["links"] = ex.get("links", {})
        groups = ex["groups"]
    elif is_json:
        entry["title"] = ""
        entry["removed"] = 0
        entry["compacted"] = 0
        entry["links"] = {}
        groups, jnote = _json_groups(text)
        if jnote:
            entry["notes"].append(jnote)
    elif cls["want_headings"]:
        entry["title"] = ""
        entry["removed"] = 0
        entry["compacted"] = 0
        groups = _md_groups(text)
        if not cls["is_md"]:
            entry["notes"].append("Grouped content by Markdown-style headings (# / setext). "
                                  "Documentation .txt files may contain Markdown.")
    else:
        entry["title"] = ""
        entry["removed"] = 0
        entry["compacted"] = 0
        entry["links"] = {}
        groups = [{"title": None, "level": None,
                  "lines": text.replace(chr(13), chr(10)).split(chr(10)), "flags": set()}]

    chunks = _finalize(groups, int(v.MAX_STORE_CHARS), entry["notes"], int(v.CHUNK_CHARS))

    if not chunks:
        entry["text"] = ""
        entry["chunks"] = []
        entry["total_chars"] = 0
        entry["total_tokens"] = 0
        if is_html:
            entry["notes"].append("No text was extracted from static HTML. The page may be a JavaScript-rendered SPA.")
        else:
            entry["notes"].append("No extractable body text was found (the response may contain only whitespace or symbols).")
        if len(text) > 400:
            entry["notes"].append("Raw response contains " + _kfmt(len(text)) + " characters; inspect its beginning with mode=raw.")
        return entry, "", meta

    entry["chunks"] = chunks
    entry["text"] = _join(chunks)
    entry["total_chars"] = sum(c["chars"] for c in chunks)
    entry["total_tokens"] = _est_tokens(entry["text"])
    return entry, "", meta


# ---------------------------------------------------------------- extract

def _extract_html(text: str, base_url: str = "") -> Dict[str, Any]:
    soup = BeautifulSoup(text, _BS_PARSER)
    title = _norm(soup.title.get_text(" ")) if soup.title else ""
    generator = soup.find("meta", attrs={"name": re.compile(r"^generator$", re.I)})
    is_mediawiki = bool(soup.select_one(".mw-parser-output, #mw-content-text") or
                        (generator and re.search(r"mediawiki", generator.get("content", ""), re.I)))
    body = soup.body or soup

    removed = 0
    compacted = 0

    def strip_elements(elements):
        """Remove selected elements and count their text once (outermost element only)."""
        nonlocal removed
        elements = list(elements)
        selected = {id(el) for el in elements}
        for el in elements:
            if any(id(parent) in selected for parent in el.parents):
                continue
            removed += len(_norm(el.get_text(" ")))
        for el in elements:
            el.decompose()

    strip_elements(body.find_all(_ALWAYS_STRIP))
    for c in body.find_all(string=lambda s: isinstance(s, Comment)):
        removed += len(_norm(str(c)))
        c.extract()

    container = _pick_container(body) or _density_fallback(body) or body

    # コンテナの祖先である nav/header/footer/aside は除去しない(消すと本文ごと飛ぶ)
    anc = {id(pp) for pp in container.parents}
    for selector in _NOISE_STRIP:
        for el in list(body.select(selector)):
            if el is container or id(el) in anc:
                continue
            strip_elements([el])

    # MediaWiki editing UI is identified structurally; never remove by visible
    # words such as "編集", which may be ordinary article text.
    edit_controls = (list(container.select(
        ".mw-editsection, .mw-editsection-visualeditor, .mw-editsection-like, .wb-editpage, .mw-empty-elt"))
        if is_mediawiki else [])
    if edit_controls:
        strip_elements(edit_controls)

    # Keep link destinations out of the extracted prose. The caller can follow a
    # page-local ID through the cached link registry instead.
    links: Dict[str, str] = {}
    infobox_targets = set()
    for a in list(container.find_all("a")):
        href = (a.get("href") or "").strip()
        label = _norm(a.get_text(" "))
        href_l = href.lower()
        classes = a.get("class", [])
        if isinstance(classes, str):
            classes = classes.split()
        class_l = {c.lower() for c in classes}
        wikidata_edit = ("wikidata.org" in href_l and
                         ("special:entitypage" in href_l or "action=edit" in href_l
                          or "wb-editpage" in class_l or "wikibase-edit" in class_l))
        if is_mediawiki and ("action=edit" in href_l or "veaction=edit" in href_l or wikidata_edit
                             or "mw-editsection" in class_l or "mw-editsection-like" in class_l):
            removed += len(label)
            a.decompose()
            continue
        if not href:
            a.unwrap()
            continue
        image = a.find("img")
        if image and not label:
            alt = _norm(image.get("alt") or "")
            label = ("Image: " + alt) if alt else "Image"
            if not alt:
                # Bare thumbnails provide no useful destination or description.
                a.decompose()
                continue
        target = urljoin(base_url, href)
        p = urlsplit(target)
        target = urlunsplit((p.scheme, p.netloc, p.path,
                             "&".join(x for x in p.query.split("&")
                                      if not re.match(r"(?i)^(utm_[^=]*|ref|source)=", x)), ""))
        is_http_target = p.scheme.lower() in ("http", "https") and bool(p.netloc)
        if is_http_target:
            next_link_id = "L" + str(len(links) + 1)
            compacted += max(0, len("[" + (label or target) + "](" + target + ")")
                             - len("[" + next_link_id + "] " + (label or "Link")))
        base = urlsplit(base_url) if base_url else None
        same_origin = bool(base and p.scheme in ("http", "https")
                           and p.scheme.lower() == base.scheme.lower()
                           and p.netloc.lower() == base.netloc.lower())
        host = (p.hostname or "").lower()
        is_map_service = any(host == d or host.endswith("." + d) for d in _MAP_LINK_HOSTS)
        map_link = is_map_service and (
            len(target) > 120 or re.search(r"(?i)(/maps?/|/m2/|[?&](lat|lon|ll|params)=)", target)
        )
        parent = a.parent
        in_infobox = False
        while parent is not None and getattr(parent, "name", None) not in ("body", "html"):
            classes = parent.get("class", []) if getattr(parent, "get", None) else []
            if isinstance(classes, str):
                classes = classes.split()
            if any("infobox" in cls.lower() for cls in classes):
                in_infobox = True
                break
            parent = getattr(parent, "parent", None)
        if is_mediawiki and in_infobox and is_map_service:
            removed += len(label)
            a.decompose()
            continue
        dedupe_key = target.lower().rstrip("/")
        if is_mediawiki and in_infobox and dedupe_key in infobox_targets:
            removed += len(label)
            a.decompose()
            continue
        if is_mediawiki and in_infobox:
            infobox_targets.add(dedupe_key)
        if is_http_target:
            link_id = "L" + str(len(links) + 1)
            links[link_id] = target
            link_label = "[" + link_id + "] " + (label or "Link")
        else:
            link_label = label or "Link"
        if same_origin:
            # The page URL is already in the response header; avoid repeating its
            # hostname in every internal Wikipedia link.
            target = urlunsplit(("", "", p.path, p.query, ""))
        if map_link:
            # Keep the displayed coordinates or map label, but drop opaque service
            # URLs that add tokens without helping explain the article.
            a.replace_with(link_label if p.scheme.lower() in ("http", "https") else (label or "Map"))
        else:
            a.replace_with(link_label)

    groups = _groups_from_blocks(_blocks(container))
    if is_mediawiki:
        seen_link_rows = set()
        for group in groups:
            kept = []
            for line in group["lines"]:
                if re.search(r"\[L\d+\]", line) and line in seen_link_rows:
                    removed += len(line)
                    continue
                kept.append(line)
                if re.search(r"\[L\d+\]", line):
                    seen_link_rows.add(line)
            group["lines"] = kept
    return {"title": title, "groups": groups, "removed": removed,
            "compacted": compacted, "links": links}


def _pick_container(body):
    for min_chars in (250, 60):
        for sel in _CONTAINERS:
            try:
                el = body if sel == "body" else body.select_one(sel)
            except Exception:
                el = None
            if el is not None and len(_norm(el.get_text(" "))) >= min_chars:
                return el
    return None


def _density_fallback(body):
    best, best_score = None, 0.0
    for el in body.find_all(["div", "section", "article", "main"]):
        txt = _norm(el.get_text(" "))
        if len(txt) < 150:
            continue
        inner = len(el.find_all(["div", "section", "p", "li", "a", "span", "nav",
                                "footer", "aside", "script", "style"]))
        score = len(txt) / (1.0 + inner)
        if score > best_score:
            best, best_score = el, score
    return best


def _blocks(container) -> List[Tuple[str, Optional[str], Optional[int], List[str], set]]:
    out = []
    for el in container.find_all(_SELECTABLE):
        name = el.name
        if name in ("ul", "ol", "dl") and el.find_parent(["ul", "ol", "dl", "li"]):
            continue
        if name in ("p", "pre", "table", "blockquote", "figure") and el.find_parent(_NESTED_SKIP):
            continue
        if name.startswith("h") and el.find_parent(["h1", "h2", "h3", "h4", "h5", "h6", "figure", "a"]):
            continue

        if name.startswith("h"):
            t = _norm(el.get_text(" "))
            if t:
                out.append(("h", t, int(name[1]), [], set()))
            continue

        if name == "pre":
            code = _code_text(el).strip("\n")
            if code:
                out.append(("b", None, None, ["```"] + code.split("\n") + ["```"], {"code"}))
            continue

        if name == "table":
            lines = []
            seen_rows = set()
            for tr in el.find_all("tr"):
                # An outer table's find_all("tr") also sees rows in nested tables.
                # Those rows belong to the inner table and otherwise get emitted again.
                if tr.find_parent("table") is not el:
                    continue
                cells = [_norm(c2.get_text(" ")) for c2 in tr.find_all(["th", "td"])
                         if c2.find_parent("tr") is tr]
                if any(cells):
                    row = " | ".join(cells)
                    # Exact duplicate rows in a table are normally template/DOM
                    # duplication. Keep the first occurrence and preserve row order.
                    if row in seen_rows:
                        continue
                    seen_rows.add(row)
                    lines.append(row)
            if lines:
                out.append(("b", None, None, lines, {"table"}))
            continue

        if name in ("ul", "ol"):
            lines = _render_list(el, 0)
            if lines:
                out.append(("b", None, None, lines, {"list"}))
            continue

        if name == "dl":
            lines = []
            for child in el.find_all(["dt", "dd"], recursive=False):
                t = _norm(child.get_text(" "))
                if t:
                    lines.append(("- " + t) if child.name == "dt" else ("   : " + t))
            if lines:
                out.append(("b", None, None, lines, {"list"}))
            continue

        if name == "figure":
            cap = el.find("figcaption")
            alts = [i2.get("alt") for i2 in el.find_all("img") if i2.get("alt")]
            t = _norm(cap.get_text(" ")) if cap else _norm(" / ".join(a for a in alts if a))
            if t:
                out.append(("b", None, None, ["Image: " + t], set()))
            continue

        t = _norm(el.get_text(" "))
        if not t:
            continue
        prefix = "> " if name == "blockquote" else ""
        out.append(("b", None, None, [prefix + ln for ln in t.split("\n")], set()))
    return out


def _code_text(el) -> str:
    """Read highlighted code without inserting separators between syntax spans."""
    out: List[str] = []
    def walk(node):
        if getattr(node, "name", None) == "br":
            out.append("\n")
            return
        if getattr(node, "name", None):
            cls = " ".join(node.get("class", [])) if hasattr(node, "get") else ""
            if node.has_attr("data-line") or re.search(r"line-number|gutter|astroid", cls, re.I):
                return
            for child in node.children:
                walk(child)
        elif getattr(node, "string", None) is not None:
            out.append(str(node.string))
    walk(el)
    return "".join(out).replace("\t", "    ").replace("\r\n", "\n").replace("\r", "\n")


def _render_list(el, depth: int) -> List[str]:
    lines: List[str] = []
    seen_link_rows = set()
    for li in el.find_all("li", recursive=False):
        dup = copy.copy(li)
        for sub in dup.find_all(["ul", "ol", "dl"], recursive=True):
            sub.extract()
        own = _norm(dup.get_text(" "))
        if own:
            line = "  " * depth + "- " + own
            link_ids = tuple(re.findall(r"\[L\d+\]", line))
            if link_ids and line in seen_link_rows:
                pass
            else:
                lines.append(line)
                if link_ids:
                    seen_link_rows.add(line)
        for sub in li.find_all(["ul", "ol"], recursive=False):
            lines.extend(_render_list(sub, depth + 1))
    return lines


def _groups_from_blocks(blocks) -> List[Dict[str, Any]]:
    groups: List[Dict[str, Any]] = []
    cur: Optional[Dict[str, Any]] = None

    def new_group(title=None, level=None):
        g = {"title": title, "level": level, "lines": [], "flags": set()}
        groups.append(g)
        return g

    for kind, title, level, lines, flags in blocks:
        if kind == "h":
            cur = new_group(title, level)
        else:
            if cur is None:
                cur = new_group(None, None)
            cur["lines"].extend(lines)
            cur["flags"].update(flags)

    # 本文を伴わない見出し(見出し直後・末尾の見出し)だけ前チャンクに寄せる。
    # 本文が1字でもある見出しは独立 chunk に残し、outline にセクション構造を見せる。
    merged: List[Dict[str, Any]] = []
    for g in groups:
        if not "\n".join(g["lines"]).strip() and merged and "\n".join(merged[-1]["lines"]).strip():
            merged[-1]["lines"].append("#" * int(g["level"] or 3) + " " + (g["title"] or ""))
            merged[-1]["flags"] |= g["flags"]
            continue
        merged.append(g)
    return [g for g in merged if "\n".join(g["lines"]).strip() or g["title"]]


def _json_groups(text: str):
    try:
        data = json.loads(text)
    except Exception as e:
        return [{"title": None, "level": None, "lines": text.split("\n"), "flags": set()}], (
            "JSON parse failed (" + type(e).__name__ + "); chunked as raw text")

    if isinstance(data, list):
        groups = [{"title": "JSON array (" + _kfmt(len(data)) + " items)", "level": 2,
                   "lines": ["Array item count: " + _kfmt(len(data))]
                            + json.dumps(data[:1], ensure_ascii=False, indent=1).split("\n"),
                   "flags": {"code"}},
                  {"title": "JSON array items (one per line)", "level": 2,
                   "lines": [json.dumps(x, ensure_ascii=False) for x in data[1:]], "flags": set()}]
        return groups, "Array items are chunked one per line; request a chunk range to retrieve several together."

    if isinstance(data, dict):
        lines = []
        for k, val in data.items():
            if isinstance(val, list):
                lines.append('- key "' + k + '": array with ' + _kfmt(len(val)) + " items")
            elif isinstance(val, dict):
                lines.append('- key "' + k + '": object (' + ", ".join(list(val.keys())[:8]) + ")")
            else:
                s = json.dumps(val, ensure_ascii=False)
                lines.append('- key "' + k + '": ' + (s if len(s) <= 200 else s[:200] + "..."))
        groups = [{"title": "JSON top-level keys", "level": 2, "lines": lines, "flags": set()}]
        for k, val in data.items():
            if isinstance(val, (list, dict)):
                groups.append({"title": "JSON key: " + k, "level": 2,
                               "lines": ["```"] + json.dumps(val, ensure_ascii=False, indent=1).split("\n") + ["```"],
                               "flags": {"code"}})
        return groups, "JSON top-level keys are listed; large values are split into separate chunks."

    body = json.dumps(data, ensure_ascii=False, indent=1)
    return [{"title": "JSON value", "level": 2, "lines": body.split("\n"), "flags": {"code"}}], "Scalar JSON value; no key list is available."


# ---------------------------------------------------------------- chunking

def _hard_split(part: str, max_chars: int, overlap: int) -> List[str]:
    """1行(1ブロック)が max_chars を超える場合の文字数強制分割。
    長い paragraph・1行JSON・minified JS・1行CSV で必要になる。"""
    out: List[str] = []
    step = max(1000, max_chars)
    pos = 0
    n = len(part)
    while pos < n:
        out.append(part[pos:pos + step])
        pos += step
        if pos >= n:
            break
        nxt = pos - overlap
        pos = nxt if nxt > (pos - step) else pos
    return out


def _split_group(g: Dict[str, Any], max_chars: int) -> List[Dict[str, Any]]:
    text = "\n".join(g["lines"]).strip()
    if max_chars <= 0 or len(text) <= max_chars:
        return [{"title": g["title"], "level": g["level"], "text": text,
                 "flags": set(g["flags"]), "split": False, "part": 0, "parts": 1}]

    raw: List[str] = []
    buf: List[str] = []
    n = 0
    for ln in g["lines"]:
        add = len(ln) + 1
        if len(ln) > max_chars:              # 単独行が上限超
            if buf:
                raw.append("\n".join(buf).strip())
                buf, n = [], 0
            raw.extend(_hard_split(ln, max_chars, 240))
            continue
        if buf and n + add > max_chars:
            raw.append("\n".join(buf).strip())
            buf, n = [], 0
        buf.append(ln)
        n += add
    if buf:
        raw.append("\n".join(buf).strip())

    parts: List[str] = []
    for p in raw:
        if len(p) > max_chars:
            parts.extend(_hard_split(p, max_chars, 240))
        elif p:
            parts.append(p)
    if not parts:
        return [{"title": g["title"], "level": g["level"], "text": text,
                 "flags": set(g["flags"]), "split": False, "part": 0, "parts": 1}]

    # 前チャンク末尾(最大2行・150字まで)を冒頭に引き継いで文脈の断絶を和らげる
    out: List[Dict[str, Any]] = []
    for i, p in enumerate(parts):
        body = p
        # Tables are already self-contained row records. Repeating preceding
        # rows as context creates duplicate data and wastes the response budget.
        if i > 0 and "table" not in g["flags"]:
            carry = "\n".join(parts[i - 1].split("\n")[-2:])
            if 0 < len(carry) <= 150 and carry not in body:
                body = carry + "\n" + body
        out.append({"title": g["title"], "level": g["level"], "text": body,
                    "flags": set(g["flags"]), "split": len(parts) > 1,
                    "part": i + 1, "parts": len(parts)})
    return out


def _head_line(g: Dict[str, Any]) -> str:
    """検索用・表示用の見出し行。分割時は (2/3) を付けて続きがある事を明示する。"""
    if not g["title"]:
        return ""
    mark = " (%d/%d)" % (g["part"], g["parts"]) if (g["split"] and g["parts"] > 1) else ""
    return "#" * int(g["level"] or 2) + " " + g["title"] + mark


def _finalize(groups: List[Dict[str, Any]], max_chars: int, notes: List[str],
              per_chunk: int = 3000) -> List[Dict[str, Any]]:
    per_chunk = max(800, int(per_chunk))
    flat: List[Dict[str, Any]] = []
    for g in groups:
        flat.extend(_split_group(g, per_chunk))

    chunks: List[Dict[str, Any]] = []
    pos = 0
    total_body = 0
    cut = False
    for g in flat:
        text = g["text"]
        if not text:
            continue
        if total_body + len(text) + 2 > max_chars:
            room = max_chars - total_body
            if room < 600:
                cut = True
                break
            g = dict(g)
            g["text"] = text = text[:room]
            g["parts"] = max(g["parts"], g["part"] + 1)
            cut = True
        head = _head_line(g)
        searchable = (head + "\n" if head else "") + text
        chunks.append({
            "id": "c" + str(len(chunks) + 1),
            "title": g["title"], "level": g["level"],
            "text": text, "search": searchable, "head": head,
            "chars": len(text), "tokens": _est_tokens(text),
            "flags": g["flags"], "split": g["split"],
            "part": g["part"], "parts": g["parts"],
            "start": pos, "end": pos + len(searchable),
        })
        pos += len(searchable) + 2
        total_body += len(text) + 2
    if cut:
            notes.append("Storage limit (MAX_STORE_CHARS) reached. Available chunks are listed in OUTLINE.")
    return chunks


def _join(chunks: Sequence[Dict[str, Any]]) -> str:
    return "\n\n".join(c["search"] for c in chunks)


# ---------------------------------------------------------------- selection

def _parse_chunk_spec(spec: str, n: int) -> Tuple[List[str], str]:
    ids = []
    for part in re.split(r"[,;]", (spec or "").strip()):
        part = part.strip().lower().replace("chunk", "").replace(" ", "")
        if not part:
            continue
        m = re.fullmatch(r"c?(\d+)(?:-c?(\d+))?", part)
        if not m:
            valid = _range_hint(["c" + str(i) for i in range(1, n + 1)]) if 0 < n <= 200 else ("1-" + str(n))
            return [], ("Could not parse chunk specification: " + repr(spec)
                        + " Examples: c3 / c3-c6 / c1,c5 / total chunks: " + str(n)
                        + " Valid IDs: " + valid)
        a, b = int(m.group(1)), int(m.group(2) or m.group(1))
        if a > b:
            a, b = b, a
        for i in range(a, b + 1):
            if 1 <= i <= n:
                ids.append("c" + str(i))
    ids = list(dict.fromkeys(ids))
    if not ids:
        valid = _range_hint(["c" + str(i) for i in range(1, n + 1)]) if 0 < n <= 200 else ("1-" + str(n))
        return [], ("Chunk specification " + repr(spec) + " is outside the valid range (1-" + str(n) + ")."
                    + " Valid IDs (examples): " + valid + " / request mode=outline for the list.")
    return ids, ""


def _chunk_of(chunks: Sequence[Dict[str, Any]], offset: int) -> str:
    starts = [c["start"] for c in chunks]
    return chunks[max(0, bisect_right(starts, offset) - 1)]["id"]


# ---------------------------------------------------------------- rendering

def _flag_note(c: Dict[str, Any]) -> str:
    s = ""
    if "table" in c["flags"]:
        s += " [table]"
    if "code" in c["flags"]:
        s += " [code]"
    if "list" in c["flags"]:
        s += " [list]"
    if c["split"] and c["parts"] > 1:
        s += " [part %d/%d]" % (c["part"], c["parts"])
    return s


def _range_hint(ids: Sequence[str]) -> str:
    nums = [int(i[1:]) for i in ids]
    out: List[str] = []
    start = prev = None
    for n in nums:
        if prev is not None and n == prev + 1:
            prev = n
            continue
        if start is not None:
            out.append("c%d" % start if start == prev else "c%d-c%d" % (start, prev))
        start, prev = n, n
    if start is not None:
        out.append("c%d" % start if start == prev else "c%d-c%d" % (start, prev))
    return ", ".join(out)


def _outline(chunks: Sequence[Dict[str, Any]], included: Sequence[str], max_rows: int = 0) -> List[str]:
    lines: List[str] = []
    omitted: List[str] = []
    for c in chunks:
        if max_rows > 0 and len(lines) >= max_rows:
            omitted.append(c["id"])
            continue
        title = (c["title"] or "(untitled)")[:70].replace("\n", " ")
        lvl = "h%d" % c["level"] if c["level"] else "-"
        star = " ★included" if c["id"] in included else ""
        lines.append("%-5s %-3s %-70s %8s chars %8s tok%s%s" % (
            c["id"], lvl, title, _kfmt(c["chars"]), _kfmt(c["tokens"]), _flag_note(c), star))
    if omitted:
        lines.append("(%d chunks omitted: %s)" % (len(omitted), _range_hint(omitted)))
    return lines


def _meta_block(entry: Dict[str, Any], cache_note: str, mode_note: str) -> List[str]:
    m = entry["meta"]
    out = ["# HTTP FETCH" + mode_note, "url: " + m["url"]]
    line = "status: " + str(m["status"]) + " | type: " + (m.get("ct") or "unknown")
    if m.get("charset"):
        line += " | charset: " + m["charset"]
    out.append(line + " | cache: " + cache_note)
    if entry.get("snapshot"):
        out.append("extractor: v" + str(entry.get("extractor_version", "?")) +
                   " | snapshot: " + entry["snapshot"])
    if m.get("hops"):
        out.append("redirect: followed " + str(m["hops"]) + " hop(s) (original URL: " + (m.get("redirected_from") or "") + ")")
    if m.get("no_location"):
        out.append("3xx response without a Location header (treated as a response with no body)")
    out.append("received: " + _kfmt(m["bytes"]) + " bytes"
               + (" (download limit reached)" if m.get("truncated") else "")
               + " | extracted: " + _kfmt(entry["total_chars"]) + " chars ≈ " + _kfmt(entry["total_tokens"]) + " tokens"
               + (" | stripped HTML text: " + _kfmt(entry.get("removed", 0)) + " chars"
                  + " | link markup compacted: " + _kfmt(entry.get("compacted", 0)) + " chars"
                  if m.get("is_html") else " | Markdown/text: source text preserved"))
    if entry.get("title"):
        out.append("title: " + entry["title"][:160])
    return out


def _next_block(chunks: Sequence[Dict[str, Any]], incl: Sequence[str], snapshot: str = "") -> List[str]:
    out = ["# NEXT"]
    nxt = int((incl[-1] if incl else "c0")[1:]) + 1
    if nxt <= len(chunks):
        out.append('- To continue, use the same url, snapshot="' + snapshot +
                   '", and chunk="c%d-c%d" (use chunk IDs, not character offsets)'
                   % (nxt, len(chunks)))
    else:
        out.append("- All chunks have been returned; no more content is available")
    out.append('- If you know a search term, use query="..." instead of chunk (headings are searched too)')
    out.append('- Follow a link with the same source url, snapshot="' + snapshot + '", and link_id="L1"')
    out.append('- Include the same snapshot with query/chunk follow-ups; it prevents stale chunk IDs from selecting different content')
    out.append('- mode="outline"=list only / mode="raw"=raw response start / mode="all"=full text within limit / refresh=true=fetch again')
    out.append("- Request only the chunks you need")
    return out


def _notes_block(notes: Sequence[str]) -> List[str]:
    if not notes:
        return []
    return ["", "# NOTES"] + list(notes)


def _render_first(entry: Dict[str, Any], cache_note: str, budget: int, max_rows: int = 0) -> str:
    chunks = entry["chunks"]
    incl: List[str] = []
    used = 0
    for c in chunks:
        if used >= budget and incl:      # 先頭 chunk は必ず同梱(中身が見えないと続ける価値を判断できない)
            break
        incl.append(c["id"])
        used += c["chars"] + 40
    out = _meta_block(entry, cache_note, "")
    out += ["", "# OUTLINE (" + str(len(chunks)) + " chunks)"]
    out += _outline(chunks, incl, max_rows)
    out += ["", "# PREVIEW (" + _kfmt(used) + " chars / chunks " + ",".join(incl) + ")"]
    for c in chunks:
        if c["id"] not in incl:
            continue
        out.append("[%s] %s%s" % (c["id"], c["head"] or "(untitled)", _flag_note(c)))
        out.append(c["text"])
        out.append("")
    out += _next_block(chunks, incl, entry.get("snapshot", ""))
    out += _notes_block(entry["notes"])
    return "\n".join(out)


def _render_outline_only(entry: Dict[str, Any], cache_note: str, max_rows: int = 0) -> str:
    chunks = entry["chunks"]
    out = _meta_block(entry, cache_note, " (outline)")
    out += ["", "# OUTLINE (" + str(len(chunks)) + " chunks)"]
    out += _outline(chunks, [], max_rows)
    out += _next_block(chunks, [], entry.get("snapshot", ""))
    out += _notes_block(entry["notes"])
    return "\n".join(out)


def _render_chunks(entry: Dict[str, Any], cache_note: str, ids: Sequence[str], budget: int) -> str:
    by_id = {c["id"]: c for c in entry["chunks"]}
    base = _meta_block(entry, cache_note, " (chunk)")
    base += ["", "Requested chunks: " + ",".join(ids) + " | response limit: " + _kfmt(budget) + " chars"]
    returned: List[str] = []

    def render(returned_ids: Sequence[str], omitted_ids: Sequence[str]) -> str:
        out = list(base)
        for cid in returned_ids:
            c = by_id[cid]
            out += ["", "[" + cid + "] " + (c["head"] or "(untitled)") + _flag_note(c), c["text"]]
        out += ["", "# CHUNK STATUS"]
        if returned_ids:
            out.append("Returned in full: " + _range_hint(returned_ids))
        if omitted_ids:
            out.append("Not returned (response limit): " + _range_hint(omitted_ids)
                       + '. Retry with chunk="' + ",".join(omitted_ids) + '" and snapshot="'
                       + str(entry.get("snapshot", "")) + '" or request fewer chunks.')
        return "\n".join(out)

    omitted = list(ids)
    for cid in ids:
        candidate = returned + [cid]
        candidate_omitted = [other for other in ids if other not in candidate]
        # Count metadata, headings and status instructions too. Return whole
        # chunks only, so the status always distinguishes complete from omitted.
        if len(render(candidate, candidate_omitted)) <= max(0, int(budget)):
            returned.append(cid)
            omitted.remove(cid)
    return render(returned, omitted)


def _render_query(entry: Dict[str, Any], cache_note: str, q: str, window: int, budget: int) -> str:
    text = entry["text"]
    chunks = entry["chunks"]
    out = _meta_block(entry, cache_note, " (query)")
    # Double quotes preserve a phrase as one literal term. Whitespace means AND;
    # explicit OR separates AND-groups, e.g. "foo bar OR baz".
    tokens = [m.group(1) if m.group(1) is not None else m.group(2)
              for m in re.finditer(r'"([^"\\]*(?:\\.[^"\\]*)*)"|(\S+)', q)]
    tokens = [t.replace('\\"', '"').strip('"') for t in tokens if t]
    regex_mode = not ('"' in q or " OR " in q.upper()) and bool(re.search(r"[|^\\[(]", q))
    groups: List[List[str]] = [[]]
    for token in tokens:
        if token.upper() == "OR":
            if groups[-1]:
                groups.append([])
            continue
        term = token[1:] if token.startswith("+") else token
        if term:
            groups[-1].append(term)
    groups = [group for group in groups if group]
    if regex_mode:
        try:
            pat = re.compile(q, re.I)
            search_note = "regex"
        except re.error:
            regex_mode = False
    if not regex_mode:
        if len(groups) > 1:
            search_note = "explicit OR (AND within each group): " + " OR ".join(" & ".join(g) for g in groups)
        elif groups and len(groups[0]) > 1:
            search_note = "all terms (AND): " + " & ".join(groups[0])
        elif '"' in q:
            search_note = "exact phrase"
        else:
            search_note = "literal"

    hit_spans = []
    if regex_mode:
        hit_spans = [mm.span() for mm in pat.finditer(text)]
    else:
        # A query matches a chunk when every term in at least one OR group is
        # present there. Windows anchor on each group's first term.
        for c in chunks:
            searchable = c["search"]
            for group in groups:
                if all(re.search(re.escape(term), searchable, re.I) for term in group):
                    hit_spans.extend((c["start"] + mm.start(), c["start"] + mm.end())
                                     for mm in re.finditer(re.escape(group[0]), searchable, re.I))
    hit_spans = sorted(set(hit_spans))
    hits = hit_spans
    if not hits:
        out += ["", "No matches for " + repr(q) + " (" + search_note
                + "; check the chunk list or try another query)", ""]
        out += _outline(chunks, [])
        return "\n".join(out)
    spans: List[List[int]] = []
    for a0, b0 in hits[:60]:
        a = max(0, a0 - window)
        b = min(len(text), b0 + window)
        if spans and a <= spans[-1][1] + 1:
            spans[-1][1] = max(spans[-1][1], b)
        else:
            spans.append([a, b])
    query_head = ["", "query=" + repr(q) + " (" + search_note + "): " + str(len(hits)) + " matches -> " + str(len(spans))
                  + " candidate windows (" + str(window) + " chars around each match)"]
    hit_chunks = {_chunk_of(chunks, a) for a, _ in hits}

    def render_query_windows(indices: Sequence[int]) -> str:
        rendered = list(out) + query_head
        shown_chunks = set()
        for idx in indices:
            a, b = spans[idx]
            seg = text[a:b].strip()
            overlapping = [c["id"] for c in chunks if c["start"] < b and c["end"] > a]
            shown_chunks.update(overlapping)
            rendered += ["", "[" + ",".join(overlapping or [_chunk_of(chunks, a)]) + "]"
                         + (" ..." if a > 0 else "") + seg + ("..." if b < len(text) else "")]
        omitted_chunks = sorted(hit_chunks - shown_chunks, key=lambda cid: int(cid[1:]))
        omitted_window_chunks = set()
        for idx, (a, b) in enumerate(spans):
            if idx not in indices:
                omitted_window_chunks.update(c["id"] for c in chunks
                                             if c["start"] < b and c["end"] > a)
        omitted_hits = hits[60:]
        omitted_window_chunks.update(_chunk_of(chunks, a) for a, _ in omitted_hits)
        omitted_chunks = sorted(set(omitted_chunks) | omitted_window_chunks,
                                key=lambda cid: int(cid[1:]))
        rendered += ["", "# CHUNK STATUS"]
        if shown_chunks:
            rendered.append("Chunks represented in query windows (partial context): " +
                            _range_hint(sorted(shown_chunks, key=lambda cid: int(cid[1:]))))
        if omitted_chunks:
            rendered.append("Omitted query windows: " + str(len(spans) - len(indices)) +
                            "; additional matches skipped at 60-hit cap: " + str(len(omitted_hits)) +
                            "; affected matching chunks (response limit or 60-window cap): " +
                            _range_hint(omitted_chunks) + '. Retry with chunk="' +
                            ",".join(omitted_chunks) + '" and snapshot="' +
                            str(entry.get("snapshot", "")) + '" for full content.')
        rendered.append("Query windows are excerpts, not full chunks; use the suggested chunk IDs for complete text.")
        return "\n".join(rendered)

    returned: List[int] = []
    for i in range(len(spans)):
        candidate = returned + [i]
        if len(render_query_windows(candidate)) <= max(0, int(budget)):
            returned.append(i)
    return render_query_windows(returned)


def _render_all(entry: Dict[str, Any], cache_note: str, limit: int) -> str:
    out = _meta_block(entry, cache_note, " (all)")
    body = entry["text"]
    out += ["", "# FULL TEXT (" + _kfmt(min(len(body), limit)) + " chars / limit " + _kfmt(limit) + " chars)"]
    out.append(body[:limit])
    if len(body) > limit:
        out += ["", "[truncated] " + _kfmt(len(body) - limit) + " chars remain; request them by chunk range"]
    out += _notes_block(entry["notes"])
    return "\n".join(out)


def _render_raw(entry: Dict[str, Any], cache_note: str, budget: int) -> str:
    if not entry.get("raw"):
        return "Raw response is not cached because this content type is not supported for extraction."
    # 生データも meta["charset"] で読む(utf-8 固定だと Shift_JIS/EUC-JP ページが化ける)
    rb = zlib.decompress(entry["raw"])
    enc = (entry.get("meta") or {}).get("charset") or "utf-8"
    enc = enc.split("->")[-1].strip() or "utf-8"          # "iso-8859-1->shift_jis" のような追記を剥ぐ
    try:
        raw = rb.decode(enc)
    except (LookupError, UnicodeDecodeError):
        raw = rb.decode("utf-8", "replace")
    out = _meta_block(entry, cache_note, " (raw)")
    out += ["", "Raw response: first " + _kfmt(min(budget, len(raw))) + " of " + _kfmt(len(raw)) + " chars", "", raw[:budget]]
    if len(raw) > budget:
        out += ["", "[truncated: " + _kfmt(len(raw) - budget) + " chars remain]"]
    urls = list(dict.fromkeys(_URL_RE.findall(raw[:12000])))
    if urls:
        out += ["", "# Links (up to 15 from the start)", "- " + "\n- ".join(urls[:15])]
    return "\n".join(out)


def _render_meta_only(entry: Dict[str, Any], cache_note: str) -> str:
    out = _meta_block(entry, cache_note, "")
    out.append("")
    if entry["meta"].get("meta_only"):
        out.append("No body returned because this content type is not supported for extraction. chunk and query are unavailable.")
    else:
        out.append("No extractable body text was found. chunk and query are unavailable.")
    out += _notes_block(entry["notes"])
    out += ["", "# NEXT", '- Use mode="raw" to inspect the beginning of the raw response',
            "- Use refresh=true to fetch again; URL variants (such as a trailing slash) share a cache entry"]
    return "\n".join(out)


# ---------------------------------------------------------------- tool

class Tools:
    class Valves(BaseModel):
        TIMEOUT: int = Field(default=15, description="HTTP request timeout in seconds")
        USER_AGENT: str = Field(
            default="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36",
            description="User-Agent header for requests (may help with 403 responses)")
        MAX_DOWNLOAD_KB: int = Field(default=1500, description="Maximum kilobytes received per request; excess data is cut off")
        CHUNK_CHARS: int = Field(default=3000, description="Target character count per chunk")
        MAX_STORE_CHARS: int = Field(default=300000, description="Maximum body characters retained in cache")
        OUTLINE_ROWS: int = Field(default=0, description="Maximum outline rows (0 = unlimited)")
        FIRST_CALL_CHARS: int = Field(default=3000, description="Approximate body characters included in the first response")
        FETCH_CHARS: int = Field(default=7000, description="Maximum response characters for follow-up chunk/query/raw calls")
        ALL_CHARS: int = Field(default=40000, description="Character limit for mode='all'")
        QUERY_WINDOW_CHARS: int = Field(default=340, description="Context characters on each side of a query match")
        MAX_CACHE_ENTRIES: int = Field(default=30, description="Maximum cached URLs (least recently used entries are evicted)")
        TTL_SECONDS: int = Field(default=900, description="Cache lifetime for successful responses, in seconds")
        NEGATIVE_TTL_SECONDS: int = Field(default=120, description="Cache lifetime for failures (0 disables failure caching)")
        MAX_REDIRECTS: int = Field(default=5, description="Maximum redirects to follow (0 disables redirects)")
        ALLOW_PRIVATE_HOSTS: str = Field(default="off", description="Private/loopback access: off=deny; self_only=allow loopback and LAN only (link-local, multicast, and CGNAT remain blocked); all=relax address-range checks")

    def __init__(self):
        self.valves = self.Valves()

    def fetch_url(self, url: str, chunk: str = "", query: str = "", mode: str = "extract",
                  refresh: bool = False, link_id: str = "", snapshot: str = "") -> str:
        """Extract a URL and return an outline with a body preview.

        Start with url only. Request a range such as chunk="c3-c6" to continue,
        or query="term" to search the cached content. To follow a link shown as
        [L1], call again with the same source URL, link_id="L1", and snapshot from the outline.
        Use the same snapshot for chunk/query follow-ups. Available modes are
        extract, outline, raw, and all. Binary formats return metadata only.
        """
        v = self.valves
        canon = _canonical(url)
        if canon is None:
            return "Invalid URL. Specify an http:// or https:// URL: " + repr(url)

        key = hashlib.sha256(canon.encode()).hexdigest()
        keys = [key]
        entry = None
        cache_note = "miss"
        neg_note = ""

        if not refresh:
            cached, left = _cache_get(key, int(v.TTL_SECONDS))
            if cached is not None:
                if "error" in cached:
                    return (cached["error"]
                            + " [cache: retaining the same failure for " + str(left) + "s; do not resend the same URL]")
                if cached.get("extractor_version") == _EXTRACTOR_VERSION and cached.get("snapshot"):
                    entry, cache_note = cached, "hit (" + str(left) + "s remaining)"
                else:
                    cache_note = "stale cache discarded"

        if entry is None:
            requested = (url or "").strip()
            if "://" not in requested:
                requested = canon          # scheme 無し入力は canon の補完結果を使う
            allow = _normalize_allow_private(v.ALLOW_PRIVATE_HOSTS)
            blocked = _blocked_host(canon, allow)
            if not blocked and requested != canon:
                blocked = _blocked_host(requested, allow)
            if blocked:
                return blocked
            entry, err, meta = _download(requested, v)
            if err and int(meta.get("status") or 0) == 404:
                slash_variant = _toggle_trailing_slash(requested)
                if slash_variant and slash_variant != requested:
                    retry_blocked = _blocked_host(slash_variant, allow)
                    if not retry_blocked:
                        retry_entry, retry_err, retry_meta = _download(slash_variant, v)
                        if not retry_err:
                            entry, err, meta = retry_entry, "", retry_meta
                        else:
                            err = retry_err + " (also tried the same URL with the trailing slash toggled after the original returned HTTP 404)"
            if err:
                code = int(meta.get("status") or 0)
                if code in _NEGATIVE_STATUSES:
                    ttl = max(30, int(v.NEGATIVE_TTL_SECONDS))
                    _cache_put([key], {"error": err, "fetched_at": time.time(),
                                      "ttl": ttl, "meta": meta}, int(v.MAX_CACHE_ENTRIES))
                return err
            keys = [key]
            final = _canonical(meta.get("final") or "")
            if final and final != canon:
                keys.append(hashlib.sha256(final.encode()).hexdigest())
                meta["final"] = final
            _cache_put(keys, entry, int(v.MAX_CACHE_ENTRIES))
            cache_note = "miss (TTL " + str(v.TTL_SECONDS) + "s)"

        chunks = entry.get("chunks") or []
        if not chunks:
            return _render_meta_only(entry, cache_note)

        if chunk or query or link_id:
            expected_snapshot = str(entry.get("snapshot", ""))
            supplied_snapshot = (snapshot or "").strip()
            if not supplied_snapshot:
                return ("This is a follow-up request. Pass snapshot=" + repr(expected_snapshot)
                        + " from the outline together with chunk, query, or link_id."
                        + " If you no longer have that outline, request mode=outline again.")
            if supplied_snapshot != expected_snapshot:
                return ("Snapshot mismatch: the cached page content has changed or expired."
                        " Request mode=outline again, then use its current snapshot and chunk/link IDs.")

        requested_link = (link_id or "").strip().upper()
        if requested_link:
            target = (entry.get("links") or {}).get(requested_link)
            if not target:
                available = ", ".join((entry.get("links") or {}).keys()) or "none"
                return ("Unknown link_id " + repr(requested_link) + " for this cached page. Available link IDs: "
                        + available + ". Fetch the source URL again to refresh its link IDs.")
            followed = self.fetch_url(target)
            return ("Followed " + requested_link + " from " + (entry.get("meta", {}).get("final") or canon)
                    + " (source cache: " + cache_note + ")\n\n" + followed)

        q = (query or "").strip()
        if q:
            return _render_query(entry, cache_note, q, int(v.QUERY_WINDOW_CHARS), int(v.FETCH_CHARS))

        spec = (chunk or "").strip()
        if spec:
            ids, errtxt = _parse_chunk_spec(spec, len(chunks))
            if errtxt:
                return errtxt
            return _render_chunks(entry, cache_note, ids, int(v.FETCH_CHARS))

        m = (mode or "extract").strip().lower()
        warn = ""
        if m not in _MODES:
            warn = ("[NOTE] Unknown mode " + repr(mode) + "; using extract. Available modes: " + ", ".join(_MODES))
            m = "extract"
        if m == "raw":
            out = _render_raw(entry, cache_note, int(v.FETCH_CHARS))
        elif m == "outline":
            out = _render_outline_only(entry, cache_note, int(v.OUTLINE_ROWS))
        elif m in ("all", "full"):
            out = _render_all(entry, cache_note, int(v.ALL_CHARS))
        else:
            out = _render_first(entry, cache_note, int(v.FIRST_CALL_CHARS), int(v.OUTLINE_ROWS))
        return (warn + chr(10) + out) if warn else out
