#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cron: 0,30 * * * *
0,30 * * * * market_alert.py
new Env('黄金与A股行情播报');

青龙订阅入口。休市自动跳过；本地预览：python market_alert.py --dry-run --force
"""

from __future__ import annotations

import argparse
import builtins
import contextlib
import csv
import importlib
import io
import json
import math
import os
import re
import sys
import tempfile
from dataclasses import dataclass, field
from datetime import date, datetime, time, timedelta, timezone
from decimal import Decimal
from html.parser import HTMLParser
from pathlib import Path
from time import perf_counter
from typing import Any, Callable
from urllib.parse import urlsplit
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError


BEIJING = timezone(timedelta(hours=8), "Asia/Shanghai")
ROOT = Path(__file__).resolve().parent
VERSION = "2026.11.19.3"
EXPECTED_SCHEDULE = "0,30 * * * *"
MARKET_NAMES = {"sge": "上金所", "a_share": "A 股", "hk_share": "港股", "hk_connect": "港股通", "us_share": "美股", "crypto": "加密货币现货"}
HKEX_CALENDAR_URL = "https://www.hkex.com.hk/-/media/HKEX-Market/Mutual-Market/Stock-Connect/Reference-Materials/Trading-Hour,-Trading-and-Settlement-Calendar/{year}-Calendar_csv_e.csv"
# 沪市 ETF 代码段含 51/52/53/56/58，深市 ETF 使用 159；不接受场外基金和 LOF 代码。
MAINLAND_ETF_PREFIXES = {"sh": ("51", "52", "53", "56", "58"), "sz": ("159",)}
SGE_URL = "https://www.sge.com.cn"
SSE_CALENDAR_URL = "https://www.sse.com.cn/disclosure/dealinstruc/closed/"
HTTP_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/130.0.0.0 Safari/537.36",
}
GOLD_SYMBOLS = {
    symbol.lower(): symbol
    for symbol in (
        "Au99.99", "Au99.95", "Au100g", "Au99.5", "iAu99.99", "iAu99.5",
        "iAu100g", "Au(T+D)", "mAu(T+D)", "Au(T+N1)", "Au(T+N2)",
    )
}
# 两家交易所分别发布的 2026 年休市安排。补班的周六、周日仍休市。
# 上金所：https://www.sge.com.cn/jjsnotice/10007108
# 上交所：https://www.sse.com.cn/disclosure/dealinstruc/closed/
HOLIDAYS_2026 = [
    ("2026-01-01", "2026-01-03"), ("2026-02-15", "2026-02-23"),
    ("2026-04-04", "2026-04-06"), ("2026-05-01", "2026-05-05"),
    ("2026-06-19", "2026-06-21"), ("2026-09-25", "2026-09-27"),
    ("2026-10-01", "2026-10-07"),
]
NO_NIGHT_2026 = [
    "2025-12-31", "2026-02-13", "2026-04-03", "2026-04-30",
    "2026-06-18", "2026-09-24", "2026-09-30",
]

# 港交所公布的港股及南向港股通日历，两者不能用同一份休市表。
# 来源为上面的 HKEX 年度 CSV；空白表示正常交易，Half Day 表示半日市。
HK_CLOSED_2026 = "01-01 02-17 02-18 02-19 04-03 04-06 04-07 05-01 05-25 06-19 07-01 10-01 10-19 12-25".split()
CONNECT_CLOSED_2026 = "01-01 01-02 02-16 02-17 02-18 02-19 02-20 02-23 04-03 04-06 04-07 05-01 05-04 05-05 05-25 06-19 07-01 09-25 10-01 10-02 10-05 10-06 10-07 10-19 12-25".split()
HK_HALF_DAYS_2026 = "02-16 12-24 12-31".split()
CONNECT_HALF_DAYS_2026 = "12-24 12-31".split()


class ConfigError(ValueError):
    pass


class CalendarError(RuntimeError):
    pass


class QuoteError(RuntimeError):
    pass


class AlreadyRunning(RuntimeError):
    pass


class NotificationError(RuntimeError):
    pass


@dataclass(frozen=True)
class Instrument:
    market: str
    symbol: str
    name: str = ""

    @property
    def label(self) -> str:
        return f"{self.name} ({self.symbol})" if self.name else self.symbol

    @property
    def is_mainland_etf(self) -> bool:
        return self.market == "a_share" and any(
            self.symbol.startswith(exchange + prefix)
            for exchange, prefixes in MAINLAND_ETF_PREFIXES.items()
            for prefix in prefixes
        )


@dataclass
class Config:
    instruments: list[Instrument]
    stock_source: str = "auto"
    timeout_seconds: float = 10
    stale_minutes: float = 10
    calendar_overrides: dict = field(default_factory=dict)


@dataclass(frozen=True)
class Session:
    market: str
    trading_day: date
    start: datetime
    end: datetime
    name: str


@dataclass
class Quote:
    instrument: Instrument
    price: float
    source: str
    fetched_at: datetime
    quoted_at: datetime | None = None
    change_pct: float | None = None
    notes: list[str] = field(default_factory=list)
    currency: str = ""
    price_text: str = ""
    fallback_source: str = ""


def log(message: str) -> None:
    print(message, flush=True)


def error_detail(exc: Exception) -> str:
    """保留可用于排查的错误种类和 HTTP 状态，不打印密钥、代理密码或响应正文。"""
    name = type(exc).__name__
    if isinstance(exc, (QuoteError, NotificationError, CalendarError)):
        return str(exc)
    if isinstance(exc, ModuleNotFoundError):
        return f"缺少 Python 依赖 {exc.name}，请检查青龙 Python3 依赖安装日志"
    response = getattr(exc, "response", None)
    if response is not None and getattr(response, "status_code", None):
        host = urlsplit(getattr(response, "url", "") or "").hostname or "行情/通知来源"
        return f"{name}：{host} 返回 HTTP {response.status_code}"
    if "timeout" in name.lower():
        return f"{name}：网络连接或读取超时"
    if name == "Push2RateLimitError":
        return "Push2RateLimitError：东方财富拒绝连接或限流"
    if "ssl" in name.lower():
        return f"{name}：TLS 连接或证书校验失败"
    if "proxy" in name.lower():
        return f"{name}：代理连接失败，请检查运行环境的代理配置"
    if "connection" in name.lower():
        return f"{name}：网络连接失败或被来源断开"
    if isinstance(exc, PermissionError):
        return "PermissionError：目录或文件没有访问权限，请检查运行状态目录"
    if isinstance(exc, json.JSONDecodeError):
        return "JSONDecodeError：来源返回了无效 JSON，可能是错误页或访问限制"
    return name


def canonical_stock(value: str) -> str:
    value = value.strip().lower()
    suffix = re.fullmatch(r"(\d{6})\.(sh|sz|bj)", value)
    if suffix:
        value = suffix[2] + suffix[1]
    match = re.fullmatch(r"(?:(sh|sz|bj))?(\d{6})", value)
    if not match:
        raise ConfigError(f"无效的 A 股或场内 ETF 代码：{value}")
    prefix, code = match.groups()
    etf_market = next((exchange for exchange, prefixes in MAINLAND_ETF_PREFIXES.items() if code.startswith(prefixes)), None)
    expected = etf_market or ("sh" if code.startswith("6") else (
        "sz" if code.startswith(("0", "3")) else (
            "bj" if code.startswith(("4", "8", "92")) else None
        )
    ))
    if not expected or (prefix and prefix != expected):
        raise ConfigError(f"A 股或场内 ETF 市场与代码不匹配：{value}")
    return expected + code


def canonical_hk(value: str) -> str:
    value = value.strip().lower()
    match = re.fullmatch(r"(?:hk)?(\d{1,5})(?:\.hk)?", value)
    if not match or int(match[1]) == 0:
        raise ConfigError(f"无效的港股代码：{value}；例如 00700 或 00700.HK")
    return "hk" + match[1].zfill(5)


def canonical_us(value: str) -> str:
    value = value.strip().upper().replace("-", ".")
    if not re.fullmatch(r"[A-Z][A-Z0-9]{0,9}(?:\.[A-Z0-9]{1,4})?", value):
        raise ConfigError(f"无效的美股代码：{value}；例如 AAPL 或 BRK.B")
    return value


def canonical_crypto(value: str) -> str:
    value = value.strip().upper().replace("-", "/")
    if "/" not in value:
        for currency in ("USDT", "USDC", "USD", "BTC", "ETH", "EUR"):
            if value.endswith(currency) and len(value) > len(currency):
                value = value[:-len(currency)] + "/" + currency
                break
    match = re.fullmatch(r"([A-Z0-9]{1,20})/([A-Z0-9]{1,10})", value)
    if not match or match[1] == match[2]:
        raise ConfigError(f"无效的现货交易对：{value}；请填写 BTC/USDT、BTC-USDT 或 BTCUSDT")
    return value


def new_york_timezone() -> ZoneInfo:
    try:
        return ZoneInfo("America/New_York")
    except ZoneInfoNotFoundError as exc:
        raise CalendarError("缺少美国时区数据，请安装新增依赖 exchange-calendars（包含 tzdata）") from exc


def load_config(environ: dict | None = None) -> Config:
    env = os.environ if environ is None else environ
    raw, filename = env.get("MARKET_ALERT_CONFIG", ""), env.get("MARKET_ALERT_CONFIG_FILE", "")
    if raw.strip() and filename.strip():
        raise ConfigError("MARKET_ALERT_CONFIG 和 MARKET_ALERT_CONFIG_FILE 只能设置一个")
    try:
        if filename.strip():
            raw = Path(filename).expanduser().read_text(encoding="utf-8-sig")
        data = json.loads(raw) if raw.strip() else {"gold": ["Au99.99"], "stocks": []}
    except (ValueError, OSError) as exc:
        raise ConfigError(f"无法读取行情配置：{type(exc).__name__}") from exc
    if not isinstance(data, dict):
        raise ConfigError("配置必须是 JSON 对象")
    allowed = {"gold", "stocks", "hk_stocks", "hk_connect", "us_stocks", "crypto", "stock_source", "timeout_seconds", "stale_minutes", "calendar_overrides"}
    unknown = set(data) - allowed
    if unknown:
        raise ConfigError(f"未知配置项：{', '.join(sorted(unknown))}")
    instruments, seen = [], set()
    for key, market in (("gold", "sge"), ("stocks", "a_share"), ("hk_stocks", "hk_share"), ("hk_connect", "hk_connect"), ("us_stocks", "us_share"), ("crypto", "crypto")):
        entries = data.get(key, [])
        if not isinstance(entries, list):
            raise ConfigError(f"{key} 必须是数组")
        for entry in entries:
            if isinstance(entry, str):
                entry = {"symbol": entry}
            if not isinstance(entry, dict) or set(entry) - {"symbol", "name", "enabled"}:
                raise ConfigError(f"{key} 中的品种配置格式错误")
            if not isinstance(entry.get("enabled", True), bool):
                raise ConfigError("enabled 必须为 true 或 false")
            symbol, name = entry.get("symbol"), entry.get("name", "")
            if not isinstance(symbol, str) or not isinstance(name, str):
                raise ConfigError("symbol 和 name 必须为字符串；股票代码需要保留前导零")
            if market == "sge":
                normalized = GOLD_SYMBOLS.get(symbol.strip().lower())
                if not normalized:
                    raise ConfigError(f"不支持的黄金合约：{symbol}")
            else:
                normalizer = {"a_share": canonical_stock, "hk_share": canonical_hk, "hk_connect": canonical_hk, "us_share": canonical_us, "crypto": canonical_crypto}[market]
                normalized = normalizer(symbol)
            # 港股通和直接港股使用同一报价，重复配置会导致同条消息出现两遍。
            identity = ("hk_share" if market == "hk_connect" else market, normalized)
            if identity in seen:
                raise ConfigError(f"关注品种重复：{normalized}")
            seen.add(identity)
            if entry.get("enabled", True):
                instruments.append(Instrument(market, normalized, name.strip()))
    source = data.get("stock_source", "auto")
    if source not in ("auto", "akshare", "tencent"):
        raise ConfigError("stock_source 必须为 auto、akshare 或 tencent")
    numbers = {}
    for key, default, minimum, maximum in (
        ("timeout_seconds", 10, 1, 60), ("stale_minutes", 10, 1, 120),
    ):
        value = data.get(key, default)
        if isinstance(value, bool) or not isinstance(value, (int, float)) or not minimum <= value <= maximum:
            raise ConfigError(f"{key} 必须在 {minimum} 到 {maximum} 之间")
        numbers[key] = float(value)
    overrides = data.get("calendar_overrides", {})
    if not isinstance(overrides, dict) or set(overrides) - {"a_share", "sge", "hk_share", "hk_connect", "us_share"}:
        raise ConfigError("calendar_overrides 仅支持 a_share、sge、hk_share、hk_connect 和 us_share")
    for market, rules in overrides.items():
        keys = {"closed_dates", "open_dates"} | ({"no_night_dates"} if market == "sge" else set())
        if market in {"hk_share", "hk_connect"}:
            keys.add("half_days")
        if not isinstance(rules, dict) or set(rules) - keys:
            raise ConfigError(f"{market} 日历覆盖配置错误")
        for key, dates in rules.items():
            if not isinstance(dates, list):
                raise ConfigError(f"{key} 必须是 YYYY-MM-DD 日期数组")
            for item in dates:
                try:
                    if not isinstance(item, str) or date.fromisoformat(item).isoformat() != item:
                        raise ValueError()
                except ValueError as exc:
                    raise ConfigError(f"无效的交易日历日期：{item}") from exc
        if set(rules.get("closed_dates", [])) & set(rules.get("open_dates", [])):
            raise ConfigError(f"{market} 同一天不能既开市又休市")
    return Config(instruments, source, calendar_overrides=overrides, **numbers)


class PageText(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.parts: list[str] = []
        self.hidden = 0

    def handle_starttag(self, tag: str, attrs: list) -> None:
        if tag in ("script", "style"):
            self.hidden += 1

    def handle_endtag(self, tag: str) -> None:
        if tag in ("script", "style"):
            self.hidden = max(0, self.hidden - 1)

    def handle_data(self, data: str) -> None:
        if not self.hidden:
            self.parts.append(data)


def html_text(html: str) -> str:
    parser = PageText()
    parser.feed(html)
    return re.sub(r"\s+", " ", " ".join(parser.parts))


def date_range(start: date, end: date) -> set[date]:
    if end < start or (end - start).days > 31:
        raise CalendarError("官方日历日期范围异常")
    return {start + timedelta(days=i) for i in range((end - start).days + 1)}


def parse_annual_calendar(html: str, year: int, market: str) -> dict:
    text = html_text(html)
    if not re.search(rf"{year}\s*年(?:度)?.{{0,20}}休市安排", text):
        raise CalendarError(f"官网尚未提供 {year} 年休市安排")
    headings = list(re.finditer(r"(?:元旦|春节|清明节|劳动节|端午节|中秋节|国庆节)(?:[、与和](?:中秋节|国庆节))?\s*[：:]", text))
    closed, no_night = set(), set()
    for i, heading in enumerate(headings):
        section = text[heading.end(): headings[i + 1].start() if i + 1 < len(headings) else heading.end() + 600]
        ranges = list(re.finditer(r"(\d{1,2})月(\d{1,2})日[^。；;]*?至\s*(?:(\d{1,2})月)?(\d{1,2})日[^。；;]*?休市", section))
        if not ranges:
            raise CalendarError(f"无法识别 {year} 年{heading[0]}休市日期")
        for interval in ranges:
            month, day, end_month, end_day = interval.groups()
            closed.update(date_range(date(year, int(month), int(day)), date(year, int(end_month or month), int(end_day))))
        if market == "sge":
            section_nights = []
            for night in re.finditer(r"(?:(\d{4})年)?(\d{1,2})月(\d{1,2})日\s*(?:[（(][^）)]*[）)]\s*)?(?:晚上|夜间)\s*(?:无夜市交易|不进行夜市交易|不进行夜盘交易)", section):
                night_year, night_month, night_day = night.groups()
                section_nights.append(date(int(night_year or year), int(night_month), int(night_day)))
            if not section_nights:
                raise CalendarError(f"无法识别 {year} 年{heading[0]}停夜盘日期")
            no_night.update(section_nights)
    holidays = {"元旦", "春节", "清明节", "劳动节", "端午节", "中秋节", "国庆节"}
    found = {name for name in holidays if any(name in heading[0] for heading in headings)}
    if found != holidays or len(closed) < 15 or (market == "sge" and len(no_night) < 6):
        raise CalendarError(f"{year} 年官方休市安排不完整，拒绝按普通工作日猜测")
    return {"closed_dates": sorted(d.isoformat() for d in closed), "no_night_dates": sorted(d.isoformat() for d in no_night)}


def parse_hk_calendar(text: str, year: int, market: str) -> dict:
    lines = text.lstrip("\ufeff").splitlines()
    if not lines or not re.search(rf"Trading Calendar of Stock Connect.*\b{year}\b", lines[0]):
        raise CalendarError(f"港交所日历标题不匹配 {year} 年")
    rows = list(csv.DictReader(io.StringIO("\n".join(lines[1:]))))
    column = "Hong Kong" if market == "hk_share" else "Southbound Trading"
    observed, closed, half = set(), [], []
    for row in rows:
        try:
            day = date.fromisoformat(row["Date"].strip())
            status = row[column].strip()
        except (KeyError, ValueError, AttributeError) as exc:
            raise CalendarError("港交所年度日历结构不完整") from exc
        if day.year != year or day.weekday() >= 5 or day in observed or status not in {"", "Holiday", "Closed", "Half Day"}:
            raise CalendarError("港交所年度日历出现未知状态或重复日期")
        observed.add(day)
        if status in {"Holiday", "Closed"}:
            closed.append(day.isoformat())
        elif status == "Half Day":
            half.append(day.isoformat())
    first = date(year, 1, 1)
    expected = {first + timedelta(days=i) for i in range((date(year + 1, 1, 1) - first).days) if (first + timedelta(days=i)).weekday() < 5}
    if observed != expected:
        raise CalendarError(f"港交所 {year} 年日历未覆盖全年工作日")
    return {"closed_dates": closed, "half_days": half}


def write_json(path: Path, data: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, delete=False) as handle:
            temporary = Path(handle.name)
            json.dump(data, handle, ensure_ascii=False, indent=2)
        os.replace(temporary, path)
    finally:
        if temporary and temporary.exists():
            temporary.unlink()


def read_json(path: Path) -> dict:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


class CalendarStore:
    def __init__(self, config: Config, state_dir: Path, *, persist: bool = True) -> None:
        self.config, self.state_dir, self.persist = config, state_dir, persist
        self.cache: dict[tuple[str, int], dict] = {}
        self.us_calendars: dict[int, Any] = {}

    def annual(self, market: str, year: int) -> dict:
        key = (market, year)
        if key in self.cache:
            return self.cache[key]
        if year == 2026 and market in {"hk_share", "hk_connect"}:
            closed = HK_CLOSED_2026 if market == "hk_share" else CONNECT_CLOSED_2026
            half = HK_HALF_DAYS_2026 if market == "hk_share" else CONNECT_HALF_DAYS_2026
            data = {"closed_dates": [f"2026-{d}" for d in closed], "half_days": [f"2026-{d}" for d in half]}
        elif year == 2026:
            closed = set().union(*(date_range(date.fromisoformat(a), date.fromisoformat(b)) for a, b in HOLIDAYS_2026))
            data = {"closed_dates": [d.isoformat() for d in closed], "no_night_dates": NO_NIGHT_2026 if market == "sge" else []}
        else:
            cache_path = self.state_dir / f"calendar-{market}-{year}.json"
            data = read_json(cache_path)
            if data.get("year") != year or data.get("market") != market or not data.get("closed_dates"):
                try:
                    data = self.fetch_annual(market, year)
                    data.update(year=year, market=market)
                    if self.persist:
                        write_json(cache_path, data)
                except Exception as exc:
                    raise CalendarError(f"无法取得 {year} 年{MARKET_NAMES[market]}官方日历（{type(exc).__name__}），请更新订阅或检查网络") from exc
        self.cache[key] = data
        return data

    def fetch_annual(self, market: str, year: int) -> dict:
        import requests

        def get(url: str) -> str:
            response = requests.get(url, headers=HTTP_HEADERS, timeout=self.config.timeout_seconds)
            response.raise_for_status()
            response.encoding = "utf-8"
            return response.text

        if market in {"hk_share", "hk_connect"}:
            return parse_hk_calendar(get(HKEX_CALENDAR_URL.format(year=year)), year, market)
        if market == "a_share":
            return parse_annual_calendar(get(SSE_CALENDAR_URL), year, market)
        for page in range(1, 7):
            html = get(f"{SGE_URL}/jjsnotice?p={page}")
            for link in re.finditer(r'<a\b[^>]*href=[\"\'](/jjsnotice/\d+)[\"\'][^>]*>([\s\S]*?)</a>', html):
                title = html_text(link[2])
                if re.search(rf"{year}\s*年度.*节假日休市安排", title):
                    return parse_annual_calendar(get(SGE_URL + link[1]), year, market)
        raise CalendarError(f"未找到上金所 {year} 年全年休市公告")

    def is_open_day(self, market: str, day: date) -> bool:
        rules = self.config.calendar_overrides.get(market, {})
        if day.isoformat() in rules.get("closed_dates", []):
            return False
        if day.isoformat() in rules.get("open_dates", []):
            return True
        if day.weekday() >= 5:
            return False
        if market == "us_share":
            return bool(self.us_calendar(day.year).is_session(day.isoformat()))
        return day.isoformat() not in self.annual(market, day.year)["closed_dates"]

    def us_calendar(self, year: int):
        if year not in self.us_calendars:
            # is_session 对日历首尾交易日之外会报错；多取前后日期以覆盖元旦休市。
            try:
                xcals = importlib.import_module("exchange_calendars")
                self.us_calendars[year] = xcals.get_calendar("XNYS", start=f"{year - 1}-12-15", end=f"{year + 1}-01-15")
            except Exception as exc:
                raise CalendarError(f"无法加载 {year} 年美股日历（{type(exc).__name__}），请安装或更新 exchange-calendars 依赖") from exc
        return self.us_calendars[year]

    def us_session(self, now: datetime) -> Session | None:
        zone = new_york_timezone()
        day = now.astimezone(zone).date()
        if not self.is_open_day("us_share", day):
            return None
        calendar = self.us_calendar(day.year)
        if calendar.is_session(day.isoformat()):
            row = calendar.schedule.loc[day.isoformat()]
            start = row["open"].to_pydatetime().astimezone(BEIJING)
            end = row["close"].to_pydatetime().astimezone(BEIJING)
        else:
            # 显式 open_dates 可用于覆盖临时停复市，时间仍按纽约当地时间。
            start = datetime.combine(day, time(9, 30), zone).astimezone(BEIJING)
            end = datetime.combine(day, time(16), zone).astimezone(BEIJING)
        if start <= now <= end:
            close = end.astimezone(zone)
            name = f"常规时段（纽约 {close:%Z}，{close:%H:%M} 收市）"
            return Session("us_share", day, start, end, name)
        return None

    def night_open(self, day: date) -> bool:
        if not self.is_open_day("sge", day):
            return False
        rules = self.config.calendar_overrides.get("sge", {})
        if day.isoformat() in rules.get("no_night_dates", []):
            return False
        if day.isoformat() in self.annual("sge", day.year).get("no_night_dates", []):
            return False
        # 普通周五有夜盘，节前最后交易日没有；次日指下一个周一至周五。
        following = day + timedelta(days=1)
        while following.weekday() >= 5:
            following += timedelta(days=1)
        return self.is_open_day("sge", following)

    def adjacent_day(self, market: str, day: date, direction: int) -> date:
        for offset in range(1, 41):
            candidate = day + timedelta(days=offset * direction)
            if self.is_open_day(market, candidate):
                return candidate
        raise CalendarError("连续 40 天未找到交易日，请检查日历")

    def session(self, market: str, now: datetime) -> Session | None:
        now = now.astimezone(BEIJING).replace(second=0, microsecond=0)
        day, minute = now.date(), now.hour * 60 + now.minute
        if market == "crypto":
            start = datetime.combine(day, time(), BEIJING)
            return Session(market, day, start, start + timedelta(days=1), "24 小时现货")
        if market == "us_share":
            return self.us_session(now)
        if market in {"hk_share", "hk_connect"}:
            if not self.is_open_day(market, day):
                return None
            half_days = self.annual(market, day.year).get("half_days", []) + self.config.calendar_overrides.get(market, {}).get("half_days", [])
            half = day.isoformat() in half_days
            periods = ((570, 720),) if half else ((570, 720), (780, 960))
            for start, end in periods:
                if start <= minute <= end:
                    midnight = datetime.combine(day, time(), BEIJING)
                    return Session(market, day, midnight + timedelta(minutes=start), midnight + timedelta(minutes=end), "半日市" if half else ("上午" if minute <= 720 else "下午"))
            return None
        if market == "a_share":
            for start, end in ((570, 690), (780, 900)):
                if start <= minute <= end and self.is_open_day(market, day):
                    midnight = datetime.combine(day, time(), BEIJING)
                    return Session(market, day, midnight + timedelta(minutes=start), midnight + timedelta(minutes=end), "日盘")
        elif 540 <= minute <= 930:
            if self.is_open_day(market, day):
                return Session(market, day, datetime.combine(day, time(9), BEIJING), datetime.combine(day, time(15, 30), BEIJING), "日盘")
        elif minute >= 1200 or minute <= 150:
            start_day = day if minute >= 1200 else day - timedelta(days=1)
            if self.night_open(start_day):
                return Session(market, self.adjacent_day(market, start_day, 1), datetime.combine(start_day, time(20), BEIJING), datetime.combine(start_day + timedelta(days=1), time(2, 30), BEIJING), "夜盘")
        return None


def number(value: Any) -> float | None:
    try:
        result = float(value)
        return result if math.isfinite(result) else None
    except (TypeError, ValueError):
        return None


def parse_datetime(value: Any, zone=BEIJING) -> datetime:
    text = str(value).strip()
    for fmt in ("%Y年%m月%d日 %H:%M:%S", "%Y-%m-%d %H:%M:%S", "%Y/%m/%d %H:%M:%S", "%Y%m%d%H%M%S"):
        try:
            return datetime.strptime(text, fmt).replace(tzinfo=zone).astimezone(BEIJING)
        except ValueError:
            continue
    raise QuoteError("源端未提供可识别的行情日期和时间")


def gold_quote(instrument: Instrument, records: list[dict], fetched_at: datetime, source: str, session: Session | None = None) -> Quote:
    candidates = []
    trading_date_used = False
    for row in records:
        price = number(row.get("现价"))
        if price is None or price <= 0:
            continue
        updated = parse_datetime(row.get("更新时间", ""))
        night_date = (
            session is not None and session.name == "夜盘"
            and updated.date() == session.trading_day
            and (updated.time() >= time(20) or updated.time() <= time(2, 30))
        )
        if night_date:
            # 上金所夜盘 delaystr 的日期是交易日；周五夜盘甚至标为下周一。
            actual_day = session.start.date() if updated.time() >= time(20) else session.end.date()
            trading_date_used = trading_date_used or actual_day != updated.date()
            updated = datetime.combine(actual_day, updated.time(), BEIJING)
        if updated > fetched_at + timedelta(minutes=2):
            raise QuoteError("源端更新时间晚于当前时间，未采用异常报价")
        try:
            point_time = time.fromisoformat(str(row["时间"]))
        except (KeyError, ValueError) as exc:
            raise QuoteError("黄金分时数据缺少有效时间") from exc
        if night_date:
            if point_time >= time(20):
                point_day = session.start.date()
            elif point_time <= time(2, 30):
                point_day = session.end.date()
            else:
                # 原始响应带全天曲线，夜盘尚未发生的日盘点不能作为最新价。
                continue
            point = datetime.combine(point_day, point_time, BEIJING)
            if point > updated:
                continue
        else:
            point = datetime.combine(updated.date(), point_time, BEIJING)
            # 上金所数据按交易日排列，20:00 在 00:00 前；须重建跨日日期再选最新点。
            if point > updated:
                point -= timedelta(days=1)
        candidates.append((point, price))
    if not candidates:
        raise QuoteError("未取得有效黄金报价（空数据、零值或非数字）")
    quoted_at, price = max(candidates, key=lambda item: item[0])
    quote = Quote(instrument, price, source, fetched_at, quoted_at)
    if trading_date_used:
        quote.notes.append("源端日期使用交易日，行情时间已按夜盘换算为北京时间")
    return quote


def tencent_symbol(instrument: Instrument) -> str:
    return "us" + instrument.symbol if instrument.market == "us_share" else instrument.symbol


def tencent_quote(instrument: Instrument, text: str, fetched_at: datetime) -> Quote:
    symbol = tencent_symbol(instrument)
    match = re.search(rf'v_{re.escape(symbol)}="([^"\r\n]*)"', text)
    if not match:
        raise QuoteError("腾讯行情未返回该股票，请检查代码或来源支持范围")
    fields = match[1].split("~")
    if len(fields) <= 32:
        raise QuoteError("股票行情结构不完整")
    expected = instrument.symbol if instrument.market == "us_share" else instrument.symbol[2:]
    returned = fields[2]
    if returned != expected and not (instrument.market == "us_share" and re.fullmatch(re.escape(expected) + r"\.(?:OQ|N|AM|A|PK|OB|O|K)", returned)):
        raise QuoteError("股票行情代码不匹配")
    price = number(fields[3])
    if price is None or price <= 0:
        raise QuoteError("股票未返回有效成交价，可能尚未成交或已停牌")
    currency, notes = "CNY", []
    zone = BEIJING
    if instrument.is_mainland_etf:
        notes.append("场内成交价，非基金净值或 IOPV 估值；按沪深交易时段播报")
    if instrument.market == "us_share":
        if len(fields) <= 35 or fields[35] != "USD":
            raise QuoteError("美股来源未提供可识别的美元报价")
        currency, zone = "USD", new_york_timezone()
        notes.append("源端纽约时间已换算为北京时间；仅播报常规交易时段")
    elif instrument.market in {"hk_share", "hk_connect"}:
        if len(fields) <= 75 or fields[75] not in {"HKD", "CNY", "USD"}:
            raise QuoteError("港股来源未提供可识别的报价币种")
        currency = fields[75]
        if instrument.market == "hk_connect":
            notes.append("按南向港股通日历播报；价格为港股原币报价，非人民币结算价")
    named = Instrument(instrument.market, instrument.symbol, instrument.name or fields[1])
    return Quote(named, price, "腾讯免费行情", fetched_at, parse_datetime(fields[30], zone), number(fields[32]), notes, currency)


def crypto_quote(instrument: Instrument, payload: dict, fetched_at: datetime, source: str) -> Quote:
    if not isinstance(payload, dict):
        raise QuoteError(f"{source} 行情结构错误")
    base, currency = instrument.symbol.split("/")
    if source == "Binance":
        if payload.get("symbol") != base + currency:
            raise QuoteError("Binance 未返回对应现货交易对")
        raw_price = payload.get("lastPrice")
        price, change = number(raw_price), number(payload.get("priceChangePercent"))
        stamp = payload.get("closeTime")
        note = "行情时间为 24 小时统计窗口截止时间"
    else:
        rows = payload.get("data", [])
        if payload.get("code") != "0" or not isinstance(rows, list) or len(rows) != 1 or not isinstance(rows[0], dict) or rows[0].get("instId") != base + "-" + currency or rows[0].get("instType") != "SPOT":
            raise QuoteError("OKX 未返回对应现货交易对")
        row = rows[0]
        raw_price = row.get("last")
        price, opening = number(raw_price), number(row.get("open24h"))
        change = (price / opening - 1) * 100 if price and opening and opening > 0 else None
        stamp = row.get("ts")
        note = "行情时间为来源快照生成时间"
    if price is None or price <= 0:
        raise QuoteError(f"{source} 未返回有效现货成交价")
    try:
        quoted_at = datetime.fromtimestamp(float(stamp) / 1000, timezone.utc).astimezone(BEIJING)
    except (TypeError, ValueError, OverflowError, OSError) as exc:
        raise QuoteError(f"{source} 未提供有效行情时间") from exc
    if quoted_at > fetched_at + timedelta(minutes=2):
        raise QuoteError(f"{source} 行情时间晚于当前时间")
    # 保留来源的十进制字符串，避免低价币归零或大额价格出现浮点尾数。
    price_text = str(raw_price)
    if len(price_text) > 80 or not re.fullmatch(r"\d+(?:\.\d+)?", price_text):
        raise QuoteError(f"{source} 返回了无法识别的现货价格格式")
    return Quote(instrument, price, f"{source} 免费现货行情", fetched_at, quoted_at, change, [note], currency, price_text)


class QuoteProvider:
    def __init__(self, config: Config, calendars: CalendarStore, state: dict) -> None:
        self.config, self.calendars, self.state = config, calendars, state
        self.ak = None
        self.primary_failed = False
        self.crypto_primary_failed = False

    def akshare(self):
        if self.ak is None:
            self.ak = importlib.import_module("akshare")
            self.ak.set_timeout((min(5, self.config.timeout_seconds), self.config.timeout_seconds))
        return self.ak

    def stock(self, instrument: Instrument) -> Quote:
        if instrument.is_mainland_etf:
            # AKShare 个股接口按 6 开头判断沪市，会把沪市 5 开头的 ETF 发往深市。
            # ETF 直接读腾讯单品种行情，同时避免分页获取全市场 ETF。
            return self.tencent(instrument)
        if self.config.stock_source != "tencent" and not self.primary_failed:
            try:
                ak = self.akshare()
                fields = dict(ak.stock_bid_ask_em(symbol=instrument.symbol[2:]).itertuples(index=False, name=None))
                price = number(fields.get("最新"))
                if price is None or price <= 0:
                    raise QuoteError("未取得有效股票现价")
                names = self.state.setdefault("stock_names", {})
                if not instrument.name and instrument.symbol not in names:
                    try:
                        info = dict(ak.stock_individual_info_em(symbol=instrument.symbol[2:]).itertuples(index=False, name=None))
                        if info.get("股票简称"):
                            names[instrument.symbol] = str(info["股票简称"])
                    except Exception:
                        pass
                named = Instrument(instrument.market, instrument.symbol, instrument.name or names.get(instrument.symbol, "A 股"))
                return Quote(named, price, "东方财富（AKShare）", datetime.now(BEIJING), change_pct=number(fields.get("涨幅")))
            except Exception as exc:
                if self.config.stock_source == "akshare":
                    raise QuoteError(f"AKShare 股票取价失败（{type(exc).__name__}）") from exc
                self.primary_failed = True
                log(f"[取价] AKShare 股票接口不可用：{error_detail(exc)}；本次切换腾讯行情")
        if self.config.stock_source == "akshare":
            raise QuoteError("本次 AKShare 股票接口不可用")
        return self.tencent(instrument)

    def tencent(self, instrument: Instrument) -> Quote:
        import requests

        response = requests.get(f"https://qt.gtimg.cn/q={tencent_symbol(instrument)}", headers={**HTTP_HEADERS, "Referer": "https://gu.qq.com/"}, timeout=self.config.timeout_seconds)
        response.raise_for_status()
        response.encoding = "gb18030"
        return tencent_quote(instrument, response.text, datetime.now(BEIJING))

    def crypto(self, instrument: Instrument) -> Quote:
        import requests

        errors = []
        base, currency = instrument.symbol.split("/")
        sources = [
            ("Binance", "https://data-api.binance.vision/api/v3/ticker/24hr", {"symbol": base + currency}),
            ("OKX", "https://www.okx.com/api/v5/market/ticker", {"instId": base + "-" + currency}),
        ]
        for source, url, params in sources:
            if source == "Binance" and self.crypto_primary_failed:
                continue
            try:
                response = requests.get(url, params=params, headers=HTTP_HEADERS, timeout=self.config.timeout_seconds)
                response.raise_for_status()
                quote = crypto_quote(instrument, response.json(), datetime.now(BEIJING), source)
                if source == "OKX":
                    quote.fallback_source = source
                    quote.notes.append("Binance 不可用，本次使用 OKX 同名现货交易对；各交易所价格可能不同")
                return quote
            except Exception as exc:
                status = getattr(getattr(exc, "response", None), "status_code", None)
                if source == "Binance" and isinstance(exc, requests.RequestException) and (status is None or status in {403, 429, 451} or status >= 500):
                    self.crypto_primary_failed = True
                detail = f"{source}：{error_detail(exc)}"
                errors.append(detail)
                log(f"[取价] {instrument.symbol} {detail}" + ("；尝试 OKX" if source == "Binance" else ""))
        raise QuoteError("现货取价失败；" + "；".join(errors))

    def gold(self, instrument: Instrument, session: Session | None) -> Quote:
        try:
            records = self.akshare().spot_realtime_sge(symbol=instrument.symbol).to_dict("records")
            if not records:
                raise ValueError("AKShare 分时表为空")
        except Exception as exc:
            log(f"[取价] {instrument.symbol} 的 AKShare 适配不可用：{error_detail(exc)}；尝试上金所公开行情")
            import requests

            response = requests.post(f"{SGE_URL}/graph/quotations", data={"instid": instrument.symbol}, headers={**HTTP_HEADERS, "Referer": SGE_URL + "/", "X-Requested-With": "XMLHttpRequest"}, timeout=self.config.timeout_seconds)
            response.raise_for_status()
            payload = response.json()
            if payload.get("heyue") != instrument.symbol or len(payload.get("times", [])) != len(payload.get("data", [])):
                raise QuoteError("上金所返回的合约或数据结构不匹配")
            records = [{"时间": t, "现价": p, "更新时间": payload.get("delaystr")} for t, p in zip(payload["times"], payload["data"])]
            source = "上金所公开行情"
        else:
            source = "上金所（AKShare）"
        quote = gold_quote(instrument, records, datetime.now(BEIJING), source, session)
        if session:
            try:
                previous = self.calendars.adjacent_day("sge", session.trading_day, -1)
                cache = self.state.setdefault("gold_closes", {})
                key = f"{instrument.symbol}:{previous.isoformat()}"
                close = number(cache.get(key))
                if close is None:
                    history = self.akshare().spot_hist_sge(symbol=instrument.symbol)
                    values = [number(row.get("close")) for row in history.to_dict("records") if str(row.get("date"))[:10] == previous.isoformat()]
                    close = values[-1] if values else None
                    if close and close > 0:
                        cache[key] = close
                        # 只保留本次各合约的前收盘价，避免多年运行积累记录。
                        self.state["gold_closes"] = {k: v for k, v in cache.items() if k.endswith(previous.isoformat())}
                if close and close > 0:
                    quote.change_pct = (quote.price / close - 1) * 100
                else:
                    quote.notes.append("前一交易日收盘价不可用，未计算涨跌幅")
            except Exception as exc:
                log(f"[取价] {instrument.symbol} 前收盘价获取失败：{error_detail(exc)}；保留现价")
                quote.notes.append("前一交易日收盘价获取失败，未计算涨跌幅")
        return quote

    def fetch(self, instrument: Instrument, session: Session | None) -> Quote:
        if instrument.market == "sge":
            return self.gold(instrument, session)
        if instrument.market == "a_share":
            return self.stock(instrument)
        if instrument.market == "crypto":
            return self.crypto(instrument)
        return self.tencent(instrument)


def quote_status(quote: Quote, session: Session | None, stale_minutes: float, *, market_closed: bool = False) -> str:
    if quote.quoted_at is not None and quote.quoted_at > quote.fetched_at + timedelta(minutes=2):
        return "报价时间异常"
    if market_closed:
        return "港股通休市" if quote.instrument.market == "hk_connect" else "休市"
    if quote.quoted_at is None:
        return "报价时间未知"
    if session and quote.instrument.market != "crypto" and quote.quoted_at < session.start:
        return "旧报价"
    age = (quote.fetched_at - quote.quoted_at).total_seconds() / 60
    return f"延迟约 {int(age)} 分钟" if age > stale_minutes else ""


def build_message(now: datetime, results: list[tuple[Instrument, Session | None, Quote | str]], warnings: list[str], config: Config, *, closed_markets: set[str] | None = None) -> tuple[str, str]:
    topic = "多市场行情" if any(item.market not in {"sge", "a_share"} for item in config.instruments) else (
        "黄金与A股/ETF行情" if any(item.is_mainland_etf for item in config.instruments) else "黄金与A股行情"
    )
    title = f"{topic} {now:%m-%d %H:%M}"
    closed_markets = closed_markets or set()
    lines = []
    for instrument, session, result in results:
        if isinstance(result, str):
            label = " ".join(instrument.label.split())
            lines.append(f"{label}｜获取失败：{' '.join(result.split())}")
            continue
        currency = result.currency or (instrument.symbol.split("/")[1] if instrument.market == "crypto" else "USD" if instrument.market == "us_share" else "HKD" if instrument.market in {"hk_share", "hk_connect"} else "CNY")
        currency_name = {"CNY": "元", "HKD": "港元", "USD": "美元"}.get(currency, currency)
        unit = "元/克" if instrument.market == "sge" else f"{currency_name}/股"
        price = f"{result.price:,.3f}" if instrument.is_mainland_etf or instrument.market in {"hk_share", "hk_connect"} else f"{result.price:,.2f}"
        if instrument.is_mainland_etf:
            unit = "元/份"
        change = f"{result.change_pct:+.2f}%" if result.change_pct is not None else "涨跌幅暂无"
        if instrument.market == "crypto":
            unit = currency
            decimal_price = Decimal(result.price_text or str(result.price))
            price = format(decimal_price, ",f")
            if "." in price:
                price = price.rstrip("0").rstrip(".")
            change = f"24h {change}"
        status = quote_status(result, session, config.stale_minutes, market_closed=instrument.market in closed_markets)
        tags = [status] if status else []
        if result.fallback_source:
            tags.append(f"备用源 {result.fallback_source}")
        suffix = f"（{' · '.join(tags)}）" if tags else ""
        label = " ".join(result.instrument.label.split())
        lines.append(f"{label}｜{price} {unit}｜{change}{suffix}")
    if warnings:
        if lines:
            lines.append("")
        lines.extend(f"日历异常｜{warning}" for warning in warnings)
    return title, "\n".join(lines)


def send_notification(title: str, content: str) -> str:
    api = getattr(builtins, "QLAPI", None)
    if api is not None and callable(getattr(api, "systemNotify", None)):
        log("[通知] 使用青龙面板通知配置：QLAPI.systemNotify")
        try:
            result = api.systemNotify({"title": title, "content": content})
        except Exception as exc:
            raise NotificationError(f"青龙面板通知接口调用失败：{error_detail(exc)}") from exc
        if not isinstance(result, dict) or result.get("code") != 200:
            code = result.get("code", "未返回状态码") if isinstance(result, dict) else "未返回状态码"
            raise NotificationError(f"青龙面板通知失败（code={code}），请在「系统设置 → 通知设置」检查配置并发送测试通知")
        log("[通知] 青龙面板返回 code=200，确认通知发送成功")
        return "青龙面板确认通知发送成功"

    log("[通知] 当前环境无 systemNotify，使用青龙脚本通知配置")
    if title in os.environ.get("SKIP_PUSH_TITLE", "").splitlines():
        raise NotificationError("消息标题被 SKIP_PUSH_TITLE 过滤，未发送通知")
    module = None
    if api is not None and callable(getattr(api, "notify", None)):
        sender = api.notify
        module = sys.modules.get("__ql_notify__")
        if module is None:
            try:
                module = importlib.import_module("__ql_notify__")
            except ModuleNotFoundError as exc:
                if exc.name != "__ql_notify__":
                    raise NotificationError(f"青龙通知模块缺少依赖：{exc.name}") from exc
        route = "QLAPI.notify"
    else:
        sender = None
        for module_name in ("__ql_notify__", "notify"):
            try:
                module = importlib.import_module(module_name)
                sender = getattr(module, "send", None)
                if callable(sender):
                    break
            except ModuleNotFoundError as exc:
                if exc.name != module_name:
                    raise NotificationError(f"青龙通知模块缺少依赖：{exc.name}") from exc
        if not callable(sender):
            raise NotificationError("未找到青龙通知模块；请通过青龙 task 运行，或使用 --dry-run 仅预览")
        route = module_name + ".send"
    configured = getattr(module, "add_notify_function", None)
    if callable(configured):
        channels = configured()
        if not channels or all(getattr(channel, "__name__", "") == "console" for channel in channels):
            raise NotificationError("青龙脚本通知没有可发送消息的渠道；面板通知与脚本通知配置不同，请检查通知配置")
        log("[通知] 已检测到脚本通知渠道：" + ", ".join(getattr(channel, "__name__", "自定义渠道") for channel in channels))
    log(f"[通知] 调用 {route}")
    try:
        result = sender(title, content)
    except Exception as exc:
        raise NotificationError(f"青龙脚本通知调用失败：{error_detail(exc)}") from exc
    if result is False or (isinstance(result, dict) and result.get("code", 200) != 200):
        raise NotificationError("青龙脚本通知模块返回发送失败，请查看上方渠道日志")
    if result is None:
        log("[通知] 脚本通知调用完成，但未返回发送结果；请查看上方渠道成功/失败日志")
        return "青龙脚本通知已调用，渠道结果以通知日志为准"
    log("[通知] 青龙脚本通知模块返回成功")
    return "青龙脚本通知模块返回成功"


def log_task_schedule() -> None:
    """手动诊断时只读检查任务实际规则，不改动面板里已有的定时任务。"""
    api = getattr(builtins, "QLAPI", None)
    reader = getattr(api, "getCronDetail", None)
    log_path = os.environ.get("real_log_path") or os.environ.get("log_path")
    if not callable(reader) or not log_path:
        log("[调度] 无法读取当前任务规则；若没有自动运行日志，请检查任务已启用且规则为 " + EXPECTED_SCHEDULE)
        return
    try:
        response = reader({"log_path": log_path})
        details = response.get("data") if isinstance(response, dict) else None
        if not isinstance(details, dict) or not isinstance(details.get("schedule"), str):
            log("[调度] 青龙未返回当前任务规则；请检查任务已启用且规则为 " + EXPECTED_SCHEDULE)
            return
        schedule = details["schedule"].strip()
        log(f"[调度] 青龙当前任务实际规则：{schedule}")
        if schedule not in (EXPECTED_SCHEDULE, "0 " + EXPECTED_SCHEDULE, "*/30 * * * *", "0 */30 * * * *"):
            log("[调度] 当前规则与半小时播报不一致；订阅更新可能保留旧任务，请将此任务规则改为 " + EXPECTED_SCHEDULE)
    except Exception as exc:
        log(f"[调度] 任务规则读取失败：{error_detail(exc)}；继续检查行情和通知")


@contextlib.contextmanager
def state_lock(state_dir: Path):
    state_dir.mkdir(parents=True, exist_ok=True)
    with (state_dir / "run.lock").open("a+b") as handle:
        try:
            if os.name == "nt":
                import msvcrt

                handle.seek(0, 2)
                if handle.tell() == 0:
                    handle.write(b"0")
                    handle.flush()
                handle.seek(0)
                msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                import fcntl

                fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as exc:
            raise AlreadyRunning("已有行情任务运行，本次跳过") from exc
        try:
            yield
        finally:
            if os.name == "nt":
                handle.seek(0)
                msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def run(config: Config, now: datetime, state_dir: Path, *, dry_run: bool = False, force: bool = False, check: bool = False, manual: bool = False, provider_factory: Callable = QuoteProvider, notify: Callable = send_notification) -> int:
    now = now.astimezone(BEIJING)
    diagnostic = force or manual
    mode = "手动诊断" if manual else ("强制运行" if force else ("配置检查" if check else "按交易时段运行"))
    log(f"[启动] v{VERSION}｜北京时间 {now:%Y-%m-%d %H:%M:%S}｜Python {sys.version.split()[0]}｜{mode}")
    log(f"[调度] 半小时频率由青龙控制，期望定时规则：{EXPECTED_SCHEDULE}；脚本不再限制运行分钟")
    log("[配置] 关注品种：" + (", ".join(item.symbol for item in config.instruments) or "空") + f"｜A 股个股来源：{config.stock_source}（国内 ETF 使用腾讯）")
    if manual:
        log("[诊断] 检测到青龙手动运行：检查全部关注品种及通知，休市也检查；不占用定时播报记录")
        log_task_schedule()
    if not config.instruments:
        log("关注列表为空或已全部停用，本次不推送")
        return 0
    calendars = CalendarStore(config, state_dir, persist=not dry_run and not check)
    active, warnings = [], []
    sessions = {}
    closed_markets = set()
    for market in dict.fromkeys(item.market for item in config.instruments):
        try:
            sessions[market] = calendars.session(market, now)
            session = sessions[market]
            name = "A 股及国内 ETF" if market == "a_share" and any(item.is_mainland_etf for item in config.instruments) else MARKET_NAMES[market]
            if session:
                log(f"[日历] {name}开市：{session.name} {session.start:%m-%d %H:%M}—{session.end:%m-%d %H:%M}，交易日 {session.trading_day}")
            else:
                closed_markets.add(market)
                log(f"[日历] {name}当前休市")
        except CalendarError as exc:
            warnings.append(str(exc))
            log(f"[日历] {exc}")
            sessions[market] = None
    for item in config.instruments:
        if diagnostic or sessions[item.market]:
            active.append((item, sessions[item.market]))
    if check:
        log(json.dumps({"beijing_time": now.isoformat(), "instruments": [item.__dict__ for item in config.instruments], "active": [item.symbol for item, _ in active], "calendar_errors": warnings, "stock_source": config.stock_source}, ensure_ascii=False, indent=2))
        return 1 if warnings else 0
    if not active:
        log("\n".join(warnings) if warnings else "当前关注品种均已休市，本次不推送")
        return 1 if warnings else 0
    manager = contextlib.nullcontext() if dry_run else state_lock(state_dir)
    with manager:
        state_path = state_dir / "state.json"
        state = read_json(state_path)
        slot = now.replace(second=0, microsecond=0).isoformat()
        if not dry_run and not diagnostic and state.get("last_slot") == slot:
            log("当前时点已推送，本次跳过")
            return 0
        provider = provider_factory(config, calendars, state)
        results, failures = [], 0
        for item, session in active:
            started = perf_counter()
            log(f"[取价] 开始获取 {item.label}")
            try:
                result = provider.fetch(item, session)
                quote_time = result.quoted_at.strftime("%Y-%m-%d %H:%M:%S") if result.quoted_at else "未提供"
                log(f"[取价] {item.symbol} 成功｜来源：{result.source}｜耗时 {perf_counter() - started:.1f} 秒｜行情时间：{quote_time}｜获取时间：{result.fetched_at:%Y-%m-%d %H:%M:%S}")
                status = quote_status(result, session, config.stale_minutes, market_closed=item.market in closed_markets)
                notes = [*result.notes, status] if status else result.notes
                if notes:
                    log(f"[取价] {item.symbol} 提示：{'；'.join(notes)}")
            except Exception as exc:
                failures += 1
                result = error_detail(exc)
                log(f"[取价] {item.symbol} 失败｜{result}｜耗时 {perf_counter() - started:.1f} 秒")
            results.append((item, session, result))
        title, content = build_message(now, results, warnings, config, closed_markets=closed_markets)
        if manual:
            title = "手动检查｜" + title
        log(f"{title}\n\n{content}")
        if dry_run:
            log("\n预览完成，未发送通知，未写入运行状态")
        else:
            receipt = notify(title, content)
            if not diagnostic:
                state["last_slot"] = slot
            write_json(state_path, state)
            log("\n[完成] " + (receipt if isinstance(receipt, str) else "通知回调完成"))
            log("[状态] 手动检查不占用定时播报记录" if diagnostic else "[状态] 已记录本次播报时点")
        return 1 if failures or warnings else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="按各自交易时段播报黄金、A 股及 ETF、港股、港股通、美股及加密货币行情")
    parser.add_argument("--dry-run", action="store_true", help="只输出消息，不通知、不写入状态")
    parser.add_argument("--force", action="store_true", help="忽略交易时段和已推送状态，用于手动验证")
    parser.add_argument("--check", action="store_true", help="检查配置和交易时段，不获取行情、不通知")
    parser.add_argument("--now", help="模拟北京时间，如 2026-11-16T10:00:00；仅用于 --dry-run 或 --check")
    args = parser.parse_args(argv)
    if args.now and not (args.dry_run or args.check):
        parser.error("--now 必须与 --dry-run 或 --check 一起使用")
    try:
        if sys.version_info < (3, 11, 5):
            raise ConfigError("当前 AKShare 需要 Python 3.11.5 或更高版本")
        config = load_config()
        now = datetime.fromisoformat(args.now) if args.now else datetime.now(BEIJING)
        if now.tzinfo is None:
            now = now.replace(tzinfo=BEIJING)
        state_dir = Path(os.environ.get("MARKET_ALERT_STATE_DIR", str(ROOT / ".market-alert"))).expanduser()
        manual = os.environ.get("real_time", "").lower() == "true" and not (args.now or args.check)
        return run(config, now, state_dir, dry_run=args.dry_run, force=args.force, check=args.check, manual=manual)
    except AlreadyRunning as exc:
        log(str(exc))
        return 0
    except (ConfigError, ValueError) as exc:
        log(f"配置错误：{exc}")
        return 2
    except Exception as exc:
        log(f"[失败] {error_detail(exc)}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
