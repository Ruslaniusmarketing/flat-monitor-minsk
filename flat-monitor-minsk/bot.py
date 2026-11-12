#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Мониторинг долгосрочной аренды квартир в Минске -> уведомления в Telegram.

Запуск:
  python bot.py               # один проход (так работает GitHub Actions)
  python bot.py --mode test   # отправить тестовое сообщение в Telegram
  python bot.py --mode dry    # пройти по площадкам и показать результат в консоли, без отправки
  python bot.py --loop 600    # работать на своём ПК: проход каждые 600 секунд

Переменные окружения:
  TELEGRAM_BOT_TOKEN  — токен от @BotFather
  TELEGRAM_CHAT_ID    — куда слать (можно несколько через запятую: личка, группа с девушкой)
"""
from __future__ import annotations

import argparse
import hashlib
import html
import json
import math
import os
import re
import time
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urljoin, urlparse, urlunparse

import requests
import yaml
from bs4 import BeautifulSoup

ROOT = Path(__file__).resolve().parent
CFG = yaml.safe_load((ROOT / "config.yaml").read_text(encoding="utf-8"))
STATE_PATH = ROOT / "data" / "state.json"

SESSION = requests.Session()
SESSION.headers.update({
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36"),
    "Accept-Language": "ru-RU,ru;q=0.9,en;q=0.6",
})
MINSK_TZ = timezone(timedelta(hours=3))
SOURCE_TITLES: dict[str, str] = {}
GEO_BUDGET = [0]
FIRST_RUN = [False]


def pages_for(sc) -> int:
    """Первый запуск — глубоко (все висящие объявления), дальше — только свежие страницы."""
    if FIRST_RUN[0]:
        return int(sc.get("first_run_pages", sc.get("pages", 1)))
    return int(sc.get("pages", 1))


def log(*a):
    print(datetime.now().strftime("%H:%M:%S"), *a, flush=True)


# ----------------------------------------------------------------------------- модель

@dataclass
class Listing:
    source: str
    id: str
    url: str
    title: str = ""
    price_usd: float | None = None
    rooms: int | None = None          # 0 = студия, -1 = комната
    area: float | None = None
    kitchen: float | None = None
    district: str = ""
    address: str = ""
    lat: float | None = None
    lon: float | None = None
    text: str = ""                    # заголовок + описание (по нему — стоп-слова)
    extra: str = ""                   # характеристики (стены, метро и т.п.)
    photo: str = ""
    owner: bool | None = None
    walls: str = ""
    geo: str = ""                     # район/микрорайон по координатам (OpenStreetMap)
    published: float | None = None    # когда опубликовано/поднято (unix-время)
    zone: str = ""
    score: int = 0
    tags: list = field(default_factory=list)
    missing: list = field(default_factory=list)

    @property
    def key(self) -> str:
        return f"{self.source}:{self.id}"


# ----------------------------------------------------------------------------- утилиты

def http_get(url: str, accept_json: bool = False):
    headers = {"Accept": "application/json, text/plain, */*"} if accept_json else {}
    host = urlparse(url).netloc
    for attempt in range(3):
        try:
            r = SESSION.get(url, headers=headers, timeout=25)
        except requests.RequestException as e:
            log(f"   сеть: {host} — {type(e).__name__}")
            time.sleep(3 + 3 * attempt)
            continue
        if r.status_code == 200:
            return r
        log(f"   HTTP {r.status_code}: {host}")
        if r.status_code in (401, 403, 404, 410):
            return None
        time.sleep(3 + 3 * attempt)
    return None


def num(v):
    if v is None or isinstance(v, bool):
        return None
    if isinstance(v, (int, float)):
        return float(v)
    s = str(v).replace("\u00a0", "").replace(" ", "")
    m = re.search(r"\d+(?:[.,]\d+)?", s)
    return float(m.group().replace(",", ".")) if m else None


def parse_dt(v):
    """ISO-строка или epoch (сек/мс) -> unix-время; None, если не разобрать."""
    if v in (None, "", 0):
        return None
    if isinstance(v, (int, float)) and not isinstance(v, bool):
        return float(v) / 1000 if v > 1e11 else float(v)
    s = str(v).strip().replace("Z", "+00:00")
    s = re.sub(r"([+-]\d{2})(\d{2})$", r"\1:\2", s)          # +0300 -> +03:00
    try:
        d = datetime.fromisoformat(s.replace(" ", "T", 1))
    except ValueError:
        return None
    if d.tzinfo is None:
        d = d.replace(tzinfo=MINSK_TZ)
    return d.timestamp()


RU_MONTHS = {"янв": 1, "фев": 2, "мар": 3, "апр": 4, "мая": 5, "май": 5, "июн": 6, "июл": 7,
             "авг": 8, "сен": 9, "окт": 10, "ноя": 11, "дек": 12}


def date_from_text(t: str):
    """«Сегодня в 12:30», «вчера в …», «3 дня назад», «10 ноября», «10.11.2026» -> unix-время."""
    low = t.lower()
    now = datetime.now(MINSK_TZ)
    if re.search(r"сегодня\s*(?:в|,)\s*\d", low) or re.search(r"\d+\s*(?:мин|час)\w*\s+назад", low):
        return now.timestamp()
    if re.search(r"вчера\s*(?:в|,)\s*\d", low):
        return now.timestamp() - 86400
    m = re.search(r"(\d+)\s*(?:дн|день|дня|дней)\w*\s+назад", low)
    if m:
        return now.timestamp() - int(m.group(1)) * 86400
    m = re.search(r"\b(\d{1,2})\.(\d{1,2})\.(\d{4})\b", low)
    cand = None
    if m:
        try:
            cand = datetime(int(m.group(3)), int(m.group(2)), int(m.group(1)), tzinfo=MINSK_TZ)
        except ValueError:
            cand = None
    if cand is None:   # ISO «2026-11-09 19:58» (neagent)
        m = re.search(r"\b(\d{4})-(\d{2})-(\d{2})\b", low)
        if m:
            try:
                cand = datetime(int(m.group(1)), int(m.group(2)), int(m.group(3)), tzinfo=MINSK_TZ)
            except ValueError:
                cand = None
    if cand is None:
        m = re.search(r"\b(\d{1,2})\s+(янв|фев|мар|апр|мая|май|июн|июл|авг|сен|окт|ноя|дек)\w*", low)
        if m:
            try:
                cand = datetime(now.year, RU_MONTHS[m.group(2)], int(m.group(1)), tzinfo=MINSK_TZ)
                if cand > now:
                    cand = cand.replace(year=now.year - 1)
            except ValueError:
                cand = None
    # дата в будущем — это, скорее всего, «свободна с …», а не дата публикации
    if cand and cand.timestamp() <= now.timestamp() + 3600 and now.timestamp() - cand.timestamp() < 400 * 86400:
        return cand.timestamp()
    return None


def to_int(v):
    n = num(v)
    return int(n) if n is not None else None


def set_param(url: str, key: str, value: str) -> str:
    p = urlparse(url)
    q = [(k, v) for k, v in parse_qsl(p.query, keep_blank_values=True) if k != key]
    q.append((key, value))
    return urlunparse(p._replace(query=urlencode(q)))


def walk(o):
    """Обход любого JSON в порядке следования (для __NEXT_DATA__)."""
    stack = [o]
    while stack:
        x = stack.pop()
        yield x
        if isinstance(x, dict):
            stack.extend(reversed(list(x.values())))
        elif isinstance(x, list):
            stack.extend(reversed(x))


def haversine(lat1, lon1, lat2, lon2) -> float:
    r = 6371.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp, dl = p2 - p1, math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(math.sqrt(a))


e = html.escape

# ----------------------------------------------------------------------------- разбор текста

DISTRICTS = ["центральн", "советск", "первомайск", "партизанск", "заводск",
             "ленинск", "октябрьск", "московск", "фрунзенск"]
RE_AREA_LABEL = re.compile(r"(?:общая\s+площадь|площадь\s+общая|общ\.\s*пл\.?)\D{0,15}?(\d{2,3}(?:[.,]\d{1,2})?)", re.I)
RE_M2 = re.compile(r"(\d{2,3}(?:[.,]\d{1,2})?)\s*(?:м²|м2|кв\.?\s?м)", re.I)
RE_KITCHEN = re.compile(r"кухн\w*\D{0,20}?(\d{1,2}(?:[.,]\d{1,2})?)\s*(?:м²|м2|кв)", re.I)
RE_USD = re.compile(r"\$\s*(\d[\d\s]{1,6}\d)|(\d[\d\s]{1,6}\d)\s*(?:\$|usd|у\.\s?е)", re.I)
RE_DISTRICT = re.compile(r"([А-Яа-яЁё]+)\s+(?:район|р-н)", re.I)
RE_EURO = re.compile(r"евро\s*-?\s*(?:двуш|двух|2\b)|евродвушк", re.I)
RE_BED_DOUBLE = re.compile(
    r"двух?\s*-?\s*спальн|большая\s+кровать|кроват\w*\s*(?:\d\s*)?(?:160|180|200)|(?:160|180)\s*[хx×*]\s*200|кровать\s+king",
    re.I)


def rooms_from_text(t: str):
    t = t.lower()
    if RE_EURO.search(t) or re.search(r"\b2\s*-?\s*х?\s*-?\s*комн|двух\s*комнат|двушк", t):
        return 2
    if re.search(r"\b1\s*-?\s*(?:но)?\s*-?\s*комн|одно\s*комнат|однушк", t):
        return 1
    if re.search(r"\b[3-5]\s*-?\s*х?\s*-?\s*комн|тр[её]х\s*комнат|тр[её]шк", t):
        return 3
    return None


def district_from_text(t: str) -> str:
    for m in RE_DISTRICT.finditer(t):
        w = m.group(1).lower()
        if any(w.startswith(d) for d in DISTRICTS):
            return m.group(1).capitalize() + " район"
    return ""


def apply_text(L: Listing, t: str):
    """Достаёт из свободного текста то, чего не хватает: площадь, комнаты, цену, район."""
    if not t:
        return
    if L.area is None:
        m = RE_AREA_LABEL.search(t)
        if m:
            L.area = num(m.group(1))
        else:
            vals = [v for v in (num(x) for x in RE_M2.findall(t)) if v and 20 <= v <= 150]
            if vals:
                L.area = max(vals)
    if L.kitchen is None:
        m = RE_KITCHEN.search(t)
        if m:
            L.kitchen = num(m.group(1))
    if L.rooms is None:
        L.rooms = rooms_from_text(t)
    if L.price_usd is None:
        for m in RE_USD.finditer(t):
            v = num((m.group(1) or m.group(2) or "").replace(" ", ""))
            if v and 30 <= v <= 5000:
                L.price_usd = v
                break
    if not L.district:
        L.district = district_from_text(t)
    if L.published is None:
        L.published = date_from_text(t)


def classify_walls(t: str) -> str:
    t = t.lower()
    if "кирпич" in t:
        return "brick"
    if "монолит" in t:
        return "monolith"
    if re.search(r"каркасно\s*-?\s*блоч|блочн", t):
        return "block"
    if re.search(r"панельн|панелька|панель\b", t):
        return "panel"
    return ""


def is_studio(L: Listing) -> bool:
    if L.rooms == 0:
        return True
    t = (L.title + " " + L.text).lower()
    return bool(re.search(r"студи", t)) and not re.search(r"евро|спальн|изолир|отдельн\w*\s+комнат", t)


# ----------------------------------------------------------------------------- источники

def src_kufar(sc) -> list[Listing]:
    out, url = [], sc["api_url"]
    for _ in range(pages_for(sc)):
        r = http_get(url, accept_json=True)
        if not r:
            break
        try:
            data = r.json()
        except ValueError:
            log("   kufar: ответ не JSON — проверь api_url")
            break
        for ad in data.get("ads", []) or []:
            L = parse_kufar(ad)
            if L:
                out.append(L)
        nxt = next((p.get("token") for p in (data.get("pagination") or {}).get("pages", [])
                    if p.get("label") == "next" and p.get("token")), None)
        if not nxt:
            break
        url = set_param(sc["api_url"], "cursor", nxt)
        time.sleep(1)
    return out


def parse_kufar(ad) -> Listing | None:
    if not ad.get("ad_id"):
        return None
    params, walls = [], []
    rooms = area = kitchen = lat = lon = None
    district = ""
    for p in ad.get("ad_parameters", []) or []:
        key, label = str(p.get("p", "")), str(p.get("pl", ""))
        v, vl = p.get("v"), p.get("vl")
        if isinstance(vl, list):
            vl = ", ".join(map(str, vl))
        if key == "coordinates" and isinstance(v, list) and len(v) == 2:
            lon, lat = num(v[0]), num(v[1])
            continue
        if label and vl not in (None, ""):
            params.append(f"{label}: {vl}")
        kl = label.lower()
        if key == "rooms" or kl.startswith("комнат"):
            rooms = 0 if "студ" in str(vl).lower() else to_int(v if v is not None else vl)
        elif key == "size" or "общая площадь" in kl:
            area = num(v if v is not None else vl)
        elif "кухн" in kl and "площад" in kl:
            kitchen = num(v if v is not None else vl)
        elif kl.startswith("район") or key == "area" or "/ район" in kl:   # Kufar: p=area, pl=«Город / Район»
            district = str(vl)
        if "стен" in kl or "тип дома" in kl or "материал" in kl:
            walls.append(str(vl))
    address = ""
    for p in ad.get("account_parameters", []) or []:
        if p.get("p") == "address":
            address = str(p.get("v", ""))
    price = ad.get("price_usd")
    price = num(price) / 100 if num(price) else None    # Kufar отдаёт цену в центах
    photo = ""
    imgs = ad.get("images") or []
    if imgs and isinstance(imgs[0], dict) and imgs[0].get("path"):
        photo = "https://rms.kufar.by/v1/gallery/" + imgs[0]["path"]
    subject = ad.get("subject", "") or ""
    body = ad.get("body_short") or ad.get("body") or ""
    return Listing(
        "kufar", str(ad["ad_id"]), ad.get("ad_link", ""), title=subject, price_usd=price,
        rooms=rooms, area=area, kitchen=kitchen, district=district, address=address,
        lat=lat, lon=lon, text=f"{subject}. {body}", extra="; ".join(params), photo=photo,
        owner=None if "company_ad" not in ad else not ad.get("company_ad"), walls=" ".join(walls),
        published=parse_dt(ad.get("list_time")),
    )


ONLINER_ROOMS = {"room": -1, "1_room": 1, "2_rooms": 2, "3_rooms": 3, "4_rooms": 4,
                 "5_rooms": 5, "6_rooms": 6}


def src_onliner(sc) -> list[Listing]:
    out = []
    for page in range(1, pages_for(sc) + 1):
        r = http_get(set_param(sc["api_url"], "page", str(page)), accept_json=True)
        if not r:
            break
        try:
            data = r.json()
        except ValueError:
            log("   onliner: ответ не JSON — проверь api_url")
            break
        for a in data.get("apartments", []) or []:
            loc = a.get("location") or {}
            rt = a.get("rent_type", "")
            rooms = ONLINER_ROOMS.get(rt)
            usd = (((a.get("price") or {}).get("converted") or {}).get("USD") or {}).get("amount")
            title = {1: "1-комнатная", 2: "2-комнатная"}.get(rooms, rt)
            out.append(Listing(
                "onliner", str(a.get("id")), a.get("url", ""), title=title, price_usd=num(usd),
                rooms=rooms, address=loc.get("address") or loc.get("user_address") or "",
                lat=num(loc.get("latitude")), lon=num(loc.get("longitude")),
                photo=a.get("photo") or "", owner=(a.get("contact") or {}).get("owner"),
                published=parse_dt(a.get("created_at") or a.get("last_time_up")),
            ))
        if page >= ((data.get("page") or {}).get("last") or 1):
            break
        time.sleep(1)
    return out


def paged(sc, parse_page) -> list[Listing]:
    """Обходит страницы выдачи list_url (параметр страницы — page_param), пока идут новые объявления."""
    out, ids = [], set()
    for n in range(1, pages_for(sc) + 1):
        url = sc["list_url"] if n == 1 else set_param(sc["list_url"], sc.get("page_param", "page"), str(n))
        r = http_get(url)
        if not r:
            break
        fresh = [L for L in parse_page(BeautifulSoup(r.text, "html.parser"), sc, url) if L.id not in ids]
        if not fresh:
            break
        ids.update(L.id for L in fresh)
        out.extend(fresh)
        time.sleep(sc.get("delay_sec", 1.5))
    return out


def src_realt(sc) -> list[Listing]:
    return paged(sc, realt_page)


def realt_page(soup, sc, base) -> list[Listing]:
    out, seen = [], set()
    tag = soup.find("script", id="__NEXT_DATA__")
    if tag and tag.string:
        try:
            data = json.loads(tag.string)
        except ValueError:
            data = None
        for o in walk(data) if data is not None else []:
            if (isinstance(o, dict) and o.get("code") and ("priceRates" in o or "price" in o)
                    and ("address" in o or "title" in o or "headline" in o)):
                L = parse_realt(o, sc)
                if L and L.id not in seen:
                    seen.add(L.id)
                    out.append(L)
    if not out and sc.get("link_regex"):
        log("   realt: в __NEXT_DATA__ объявлений не нашёл, беру ссылки со страницы")
        out = generic_from_soup(soup, sc, base)
    return out


def parse_realt(o, sc) -> Listing | None:
    code = o.get("code")
    pr = o.get("priceRates") or {}
    price = pr.get("840") or pr.get(840)
    if price is None and str(o.get("priceCurrency")) == "840":
        price = o.get("price")
    lat = lon = None
    loc = o.get("location")
    if isinstance(loc, (list, tuple)) and len(loc) == 2 and num(loc[0]) and num(loc[1]):
        a, b = num(loc[0]), num(loc[1])
        lat, lon = (a, b) if a > b else (b, a)        # в Минске широта ~53.9 > долгота ~27.5
    elif isinstance(loc, dict):
        lat = num(loc.get("lat") or loc.get("latitude"))
        lon = num(loc.get("lng") or loc.get("lon") or loc.get("longitude"))
    photo = ""
    imgs = o.get("images") or o.get("photos") or []
    if isinstance(imgs, list) and imgs:
        f = imgs[0]
        photo = f if isinstance(f, str) else (f.get("url") or f.get("src") or "") if isinstance(f, dict) else ""
    extra, walls = [], []
    for k, v in o.items():
        if isinstance(v, (str, int, float)) and not isinstance(v, bool):
            if re.search(r"wall|house|building|material", k, re.I):
                walls.append(str(v))
            if re.search(r"metro|district|microdistrict|layout|repair|furniture", k, re.I):
                extra.append(str(v))
    url = o.get("url") or sc.get("item_url", "https://realt.by/rent-flat-for-long/object/{code}/").format(code=code)
    title = o.get("title") or o.get("headline") or ""
    owner = None
    agency_keys = [k for k in o if re.search(r"agenc|realtor|company", k, re.I)]
    if any(o.get(k) for k in agency_keys):
        owner = False
    elif str(o.get("sellerType") or o.get("ownerType") or "").lower() in ("owner", "private", "собственник"):
        owner = True
    return Listing(
        "realt", str(code), urljoin("https://realt.by/", url), title=str(title),
        price_usd=num(price), rooms=to_int(o.get("rooms")), area=num(o.get("areaTotal")),
        kitchen=num(o.get("areaKitchen")), district=str(o.get("townDistrictName") or ""),
        address=str(o.get("address") or ""), lat=lat, lon=lon,
        text=f"{title}. {o.get('description') or ''}", extra="; ".join(extra),
        photo=photo or "", walls=" ".join(walls), owner=owner,
        published=parse_dt(o.get("createdAt") or o.get("publishedAt") or o.get("updatedAt")),
    )


def generic_from_soup(soup, sc, base) -> list[Listing]:
    rx = re.compile(sc["link_regex"])
    found: dict[str, tuple] = {}
    maxlen = sc.get("card_max_chars", 700)
    cards = soup.select(sc["card_selector"]) if sc.get("card_selector") else None
    anchors = []
    if cards:
        for c in cards:
            a = c.find("a", href=re.compile(sc["link_regex"])) or c.find("a", href=True)
            if a:
                anchors.append((a, c))
    else:
        def ids_in(node):
            ids = set()
            for x in node.find_all("a", href=True):
                mm = rx.search(urljoin(base, x["href"]))
                if mm:
                    ids.add(mm.group(1) if mm.groups() else mm.group(0))
            return ids

        for a in soup.find_all("a", href=True):
            if not rx.search(urljoin(base, a["href"])):
                continue
            card = a
            # поднимаемся до карточки, но не выше блока, где начинаются чужие объявления
            while (card.parent is not None and card.parent.name not in ("body", "html")
                   and len(card.parent.get_text(" ", strip=True)) <= maxlen
                   and len(ids_in(card.parent)) <= 1):
                card = card.parent
            anchors.append((a, card))
    for a, card in anchors:
        href = urljoin(base, a["href"]).split("#")[0]
        m = rx.search(href)
        if not m:
            continue
        lid = m.group(1) if m.groups() else hashlib.md5(href.encode()).hexdigest()[:12]
        text = card.get_text(" ", strip=True)
        if lid not in found or len(text) > len(found[lid][1]):
            found[lid] = (href, text, card)
    out = []
    for lid, (href, text, card) in found.items():
        img = card.find("img")
        photo = urljoin(base, img.get("data-src") or img.get("src") or "") if img else ""
        L = Listing(sc["name"], lid, href, title=text[:90], text=text,
                    photo="" if photo.startswith("data:") else photo)
        apply_text(L, text)
        out.append(L)
    return out


def src_generic(sc) -> list[Listing]:
    return paged(sc, generic_from_soup)


FETCHERS = {"kufar": src_kufar, "onliner": src_onliner, "realt": src_realt, "generic": src_generic}

# ----------------------------------------------------------------------------- обогащение

DEFAULT_DETAIL_SELECTORS = ['meta[property="og:description"]', 'meta[name="description"]',
                            '[itemprop="description"]', "h1"]


def enrich_detail(L: Listing, sc):
    """Открывает страницу объявления и берёт описание/характеристики по CSS-селекторам из config."""
    if not L.url:
        return
    r = http_get(L.url)
    if not r:
        return
    soup = BeautifulSoup(r.text, "html.parser")
    parts: list[str] = []
    for sel in list(sc.get("detail_selectors") or []) + DEFAULT_DETAIL_SELECTORS:
        try:
            els = soup.select(sel)
        except Exception:
            continue
        for el in els[:3]:
            t = el.get("content", "") if el.name == "meta" else el.get_text(" ", strip=True)
            if t and t not in parts:
                parts.append(t)
    txt = " | ".join(parts)[:8000]
    if txt:
        L.text = (L.text + " | " + txt).strip(" |")
        apply_text(L, txt)
    if not L.photo:
        og = soup.find("meta", property="og:image")
        if og and og.get("content"):
            L.photo = og["content"]


def reverse_geo(L: Listing, st):
    """Район и микрорайон по координатам через OpenStreetMap (Nominatim), с кэшем."""
    if not CFG["geo"].get("enabled", True) or L.lat is None or L.lon is None:
        return
    key = f"{L.lat:.4f},{L.lon:.4f}"
    if key not in st["geo"]:
        if GEO_BUDGET[0] <= 0:
            return
        GEO_BUDGET[0] -= 1
        try:
            r = requests.get(
                "https://nominatim.openstreetmap.org/reverse",
                params={"format": "jsonv2", "lat": L.lat, "lon": L.lon, "zoom": 17, "accept-language": "ru"},
                headers={"User-Agent": "flat-monitor-minsk/1.0 (personal apartment search)"}, timeout=20)
            a = r.json().get("address", {}) if r.status_code == 200 else {}
        except (requests.RequestException, ValueError):
            a = {}
        time.sleep(1.1)
        st["geo"][key] = {
            "d": a.get("city_district", ""),
            "n": ", ".join(x for x in (a.get("suburb"), a.get("neighbourhood"), a.get("quarter")) if x),
            "a": " ".join(x for x in (a.get("road"), a.get("house_number")) if x),
        }
    g = st["geo"][key]
    L.geo = ", ".join(x for x in (g.get("d"), g.get("n")) if x)
    if not L.district and g.get("d"):
        L.district = g["d"]
    if not L.address and g.get("a"):
        L.address = g["a"]


# ----------------------------------------------------------------------------- фильтр и рейтинг

RE_NOT_AGENCY = re.compile(
    r"без\s+(?:посредник|комисси|агент|риел|риэл|переплат)\w*|не\s+(?:агентство|агент|риелтор|риэлтор|посредник)\w*", re.I)


def is_agency(L: Listing) -> bool:
    if L.owner is False:                     # площадка сама пометила: компания / агент
        return True
    t = RE_NOT_AGENCY.sub(" ", (L.title + " " + L.text).lower())
    return bool(re.search(CFG["filters"]["agency_regex"], t, re.I))


def hard_filter(L: Listing):
    f = CFG["filters"]
    t = (L.title + " " + L.text).lower()
    if L.price_usd is not None:
        if L.price_usd > f["max_price_usd"]:
            return False, "дороже бюджета"
        if L.price_usd < f["min_price_usd"]:
            return False, "слишком дёшево (посуточно/комната)"
    if L.rooms is not None and L.rooms not in f["rooms"]:
        return False, "не 1–2 комнаты"
    if re.search(f["exclude_regex"], t, re.I):
        return False, "стоп-слово"
    if CFG["filters"].get("exclude_agencies", True) and is_agency(L):
        return False, "агентство"
    if is_studio(L):
        return False, "студия"
    place = " ".join([L.district, L.address, L.geo]).lower()
    if any(x in place for x in f["exclude_districts"]):
        return False, "исключённый район"
    if L.area is not None and not (f["area_min"] <= L.area <= f["area_max"]):
        return False, "площадь вне диапазона"
    return True, ""


def detect_zone(L: Listing):
    hay = " ".join([L.address, L.district, L.geo, L.title, L.text, L.extra]).lower()
    best = None
    for z in CFG["priority_zones"]:
        hit = any(k in hay for k in z.get("keywords", []))
        if not hit and L.lat and L.lon:
            hit = any(haversine(L.lat, L.lon, p[0], p[1]) <= z.get("radius_km", 1.2) for p in z.get("points", []))
        if hit and (best is None or z["weight"] > best["weight"]):
            best = z
    return best


def score(L: Listing):
    w = CFG["scoring"]
    s, tags, missing = 0, [], []
    z = detect_zone(L)
    if z:
        s += z["weight"]
        L.zone = z["name"]
    hay = " ".join([L.title, L.text, L.extra]).lower()
    walls = classify_walls(L.walls + " " + hay)
    if walls == "brick":
        s += w["brick"]; tags.append("🧱 кирпич")
    elif walls == "monolith":
        s += w["monolith"]; tags.append("🏗 монолит")
    elif walls == "block":
        s += w["block"]; tags.append("⚠️ блочный")
    elif walls == "panel":
        s += w["panel"]; tags.append("▫️ панель")
    else:
        missing.append("стены")
    if RE_BED_DOUBLE.search(hay):
        s += w["double_bed"]; tags.append("🛏 двуспальная")
    elif "кроват" in hay:
        tags.append("🛏 кровать (размер?)")
    elif re.search(r"без\s+мебели", hay):
        s += w["no_furniture"]; tags.append("🚫 без мебели")
    elif "диван" in hay:
        s += w["sofa_only"]; tags.append("🛋 только диван?")
    else:
        missing.append("кровать")
    if RE_EURO.search(hay) or L.rooms == 2:
        s += w["isolated_bedroom"]; tags.append("🚪 спальня отдельно")
    lo, hi = w["ideal_area"]
    if L.area is None:
        missing.append("площадь")
    elif lo <= L.area <= hi:
        s += w["ideal_area_bonus"]
    if L.owner:
        s += w["owner"]; tags.append("👤 собственник")
    L.score, L.tags, L.missing = s, tags, missing


def fingerprint(L: Listing):
    a = L.address.lower()
    a = re.sub(r"беларусь|минск|г\.|ул\.|улица|проспект|пр-т|пр\.|просп\.|д\.|дом", "", a)
    a = re.sub(r"[^а-яёa-z0-9]", "", a)
    if len(a) < 5 or not L.price_usd:
        return None
    return f"{a}:{int(L.price_usd // 25)}"


def kind_of(L: Listing) -> str:
    if RE_EURO.search(L.title + " " + L.text):
        return "Евродвушка"
    return {1: "1-комн.", 2: "2-комн."}.get(L.rooms, "Квартира")


def age_days(L: Listing):
    if L.published is None:
        return None
    return max(0.0, (time.time() - L.published) / 86400)


def is_fresh(L: Listing) -> bool:
    d = age_days(L)
    return d is not None and d < CFG["send"].get("fresh_days", 3)


def age_label(L: Listing) -> str:
    d = age_days(L)
    if d is None:
        return "📅 дата публикации не указана"
    n = int(d)
    when = "сегодня" if n == 0 else ("вчера" if n == 1 else f"{n} дн. назад")
    if is_fresh(L):
        return f"🆕 <b>Свежее</b> · опубликовано {when}"
    return f"🕰 Старое · висит {n} дн."


def fmt(L: Listing) -> str:
    sc = CFG["scoring"]
    tier = "🔥" if L.score >= sc["hot"] else ("✅" if L.score >= sc["good"] else "🟡")
    head = [f"{tier} <b>{kind_of(L)}</b>"]
    if L.area:
        head.append(f"{L.area:g} м²")
    if L.price_usd:
        head.append(f"<b>${L.price_usd:,.0f}</b>".replace(",", " "))
    lines = [age_label(L), " · ".join(head)]
    if L.title and L.source != "onliner":
        lines.append(f"<i>{e(L.title[:100])}</i>")
    place = L.address
    if L.district and L.district.lower()[:6] not in place.lower():
        place = f"{place}, {L.district}" if place else L.district
    if not place:
        place = L.geo
    if place:
        lines.append("📍 " + e(place[:160]))
    if L.zone:
        lines.append("⭐ " + e(L.zone))
    if L.tags:
        lines.append(" · ".join(L.tags))
    if L.missing:
        lines.append("❔ не указано: " + ", ".join(L.missing))
    src = SOURCE_TITLES.get(L.source, L.source)
    lines.append(f'<a href="{e(L.url, quote=True)}">Открыть на {e(src)}</a> · рейтинг {L.score}')
    return "\n".join(lines)


# ----------------------------------------------------------------------------- Telegram

def chat_ids() -> list[str]:
    return [c.strip() for c in os.environ.get("TELEGRAM_CHAT_ID", "").split(",") if c.strip()]


def tg_call(method: str, payload: dict) -> dict:
    token = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
    if not token:
        raise SystemExit("Нет TELEGRAM_BOT_TOKEN — добавь секрет в настройках репозитория")
    for _ in range(3):
        try:
            r = requests.post(f"https://api.telegram.org/bot{token}/{method}", data=payload, timeout=30)
            j = r.json()
        except (requests.RequestException, ValueError) as ex:
            log(f"   telegram: {type(ex).__name__}")   # без URL, чтобы токен не попал в лог
            time.sleep(3)
            continue
        if j.get("ok"):
            return j
        if j.get("error_code") == 429:
            time.sleep(int((j.get("parameters") or {}).get("retry_after", 5)) + 1)
            continue
        log(f"   telegram {method}: {j.get('error_code')} {j.get('description')}")
        return j
    return {"ok": False}


def tg_text(text: str) -> bool:
    ok = True
    for cid in chat_ids():
        j = tg_call("sendMessage", {"chat_id": cid, "text": text, "parse_mode": "HTML",
                                    "disable_web_page_preview": "true"})
        ok = ok and bool(j.get("ok"))
    return ok


def tg_listing(L: Listing) -> bool:
    text, ok = fmt(L), True
    for cid in chat_ids():
        j = {"ok": False}
        if L.photo and len(text) <= 1024:
            j = tg_call("sendPhoto", {"chat_id": cid, "photo": L.photo, "caption": text, "parse_mode": "HTML"})
        if not j.get("ok"):
            j = tg_call("sendMessage", {"chat_id": cid, "text": text, "parse_mode": "HTML"})
        ok = ok and bool(j.get("ok"))
        time.sleep(1.2)
    return ok


# ----------------------------------------------------------------------------- состояние

def load_state() -> dict:
    st = {}
    if STATE_PATH.exists():
        try:
            st = json.loads(STATE_PATH.read_text(encoding="utf-8"))
        except ValueError:
            st = {}
    for k in ("seen", "fp", "geo"):
        st.setdefault(k, {})
    return st


def save_state(st: dict):
    STATE_PATH.parent.mkdir(exist_ok=True)
    cutoff = time.time() - CFG["state"]["keep_days"] * 86400
    st["seen"] = {k: v for k, v in st["seen"].items() if v >= cutoff}
    st["fp"] = {k: v for k, v in st["fp"].items() if v.get("t", 0) >= cutoff}
    if len(st["geo"]) > 4000:
        st["geo"] = dict(list(st["geo"].items())[-3000:])
    STATE_PATH.write_text(json.dumps(st, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")


# ----------------------------------------------------------------------------- основной проход

def run_once(mode: str = "run"):
    st = load_state()
    first = not st["seen"]
    now = int(time.time())
    FIRST_RUN[0] = first
    GEO_BUDGET[0] = CFG["geo"]["budget_first_run" if first else "budget"]
    if first:
        log("Первый запуск: разбираю всё, что сейчас опубликовано (это дольше обычного прохода)")

    candidates: list[Listing] = []
    for sc in CFG["sources"]:
        if not sc.get("enabled", True):
            continue
        SOURCE_TITLES[sc["name"]] = sc.get("title", sc["name"])
        try:
            items = FETCHERS[sc["type"]](sc)
        except Exception as ex:
            log(f"[{sc['name']}] ошибка: {type(ex).__name__}: {ex}")
            continue
        uniq: dict[str, Listing] = {}
        for L in items:
            uniq.setdefault(L.key, L)
        items = list(uniq.values())
        new = [L for L in items if L.key not in st["seen"]]
        pre, rejected = [], 0
        for L in new:
            ok, _ = hard_filter(L)
            if ok:
                pre.append(L)
            else:
                rejected += 1
                st["seen"][L.key] = now
        # что не успели проверить в этот раз, остаётся непросмотренным и разберётся следующими проходами
        limit = sc.get("first_run_detail_limit", 150) if first else sc.get("detail_limit", 25)
        take = pre[:limit]
        if sc.get("fetch_details", True):
            for L in take:
                enrich_detail(L, sc)
                time.sleep(sc.get("delay_sec", 1.5))
        candidates.extend(take)
        log(f"[{sc['name']}] всего {len(items)} · новых {len(new)} · отсеяно сразу {rejected} · на проверку {len(take)}")

    passed: list[Listing] = []
    reasons: dict[str, int] = {}
    for L in candidates:
        reverse_geo(L, st)
        ok, why = hard_filter(L)
        if not ok:
            reasons[why] = reasons.get(why, 0) + 1
            st["seen"][L.key] = now
            continue
        score(L)
        fp = fingerprint(L)
        if fp and fp in st["fp"] and st["fp"][fp].get("k") != L.key:
            reasons["дубль с другой площадки"] = reasons.get("дубль с другой площадки", 0) + 1
            st["seen"][L.key] = now
            continue
        snd = CFG["send"]
        if L.score < snd["min_score"] or (snd.get("only_priority_zones") and not L.zone):
            reasons["низкий рейтинг/не приоритетный район"] = reasons.get("низкий рейтинг/не приоритетный район", 0) + 1
            st["seen"][L.key] = now
            continue
        passed.append(L)
    # сначала свежие (до fresh_days), внутри — по рейтингу; старые тоже присылаются, но после
    passed.sort(key=lambda x: (is_fresh(x), x.score, -(x.price_usd or 999)), reverse=True)
    n_fresh = sum(1 for x in passed if is_fresh(x))
    log(f"Подходит: {len(passed)} (свежих {n_fresh}) · отсеяно после проверки: {reasons or 'нет'}")

    # всё подходящее идёт карточками; если больше лимита — остаток уйдёт следующими проходами
    limit = CFG["send"]["first_run_limit"] if first else CFG["send"]["max_per_run"]
    to_send = passed[:limit]

    if mode == "dry":
        for L in to_send:
            print("-" * 60)
            print(re.sub(r"<[^>]+>", "", fmt(L)))
        log("Режим dry: в Telegram ничего не отправлено, состояние не сохранено")
        return

    if first:
        tg_text(f"🏠 <b>Мониторинг квартир запущен</b>\nСейчас подходит {len(passed)} вариантов: "
                f"свежих (до {CFG['send'].get('fresh_days', 3)} дней) — {n_fresh}, старых — {len(passed) - n_fresh}. "
                "Присылаю все: сначала свежие, потом старые. Дальше пишу только о новых.\n"
                "🆕 — свежее, 🕰 — висит давно.\n"
                "🔥 — приоритетный район + хорошие признаки, ✅ — подходит, 🟡 — проверить вручную.")

    def mark(L):
        st["seen"][L.key] = now
        fp = fingerprint(L)
        if fp:
            st["fp"][fp] = {"k": L.key, "t": now}

    sent = 0
    for L in to_send:
        if tg_listing(L):
            sent += 1
            mark(L)
    log(f"Отправлено в Telegram: {sent} карточек")
    save_state(st)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", default="run", choices=["run", "test", "dry"])
    ap.add_argument("--loop", type=int, default=0, help="секунды между проходами (для запуска на своём ПК)")
    args = ap.parse_args()
    if args.mode == "test":
        f = CFG["filters"]
        ok = tg_text(f"✅ <b>Бот подключён</b>\nИщу: {', '.join(map(str, f['rooms']))}-комн., "
                     f"{f['area_min']}–{f['area_max']} м², до ${f['max_price_usd']}.\n"
                     f"Площадки: {', '.join(s.get('title', s['name']) for s in CFG['sources'] if s.get('enabled', True))}")
        raise SystemExit(0 if ok else 1)
    while True:
        run_once(args.mode)
        if not args.loop:
            break
        log(f"Следующий проход через {args.loop} сек")
        time.sleep(args.loop)


if __name__ == "__main__":
    main()
