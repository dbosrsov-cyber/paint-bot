import base64
import io
import json
import math
import os
import queue
import random
import re
import threading
import time
import uuid
import asyncio
import datetime
import html
import hashlib
import heapq
import hmac
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, parse_qsl
from array import array
from collections import deque
import urllib.error
import urllib.request

from PIL import Image
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, InputMediaPhoto, MessageEntity, Update, WebAppInfo
from telegram.error import BadRequest, Forbidden
from telegram.ext import Application, CallbackQueryHandler, ChatMemberHandler, CommandHandler, ContextTypes, MessageHandler, filters

# Токен бота берётся из переменной окружения BOT_TOKEN (задаётся в панели Render)
BOT_TOKEN = os.environ["BOT_TOKEN"]


def tg_init_data_valid(init_data: str) -> bool:
    """Проверка подписи Telegram WebApp (initData) по стандарту TG: HMAC-SHA256.
    Без валидной подписи сервер не принимает ни одного POST-действия —
    так игра невозможна вне Telegram, даже напрямую через curl."""
    if not BOT_TOKEN or BOT_TOKEN == "fake":
        return True                       # тестовый контур — проверка отключена
    try:
        pairs = dict(parse_qsl(init_data, keep_blank_values=True))
        received = pairs.pop("hash", "")
        if not received:
            return False
        data_check_string = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
        secret = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
        calculated = hmac.new(secret, data_check_string.encode(), hashlib.sha256).hexdigest()
        return hmac.compare_digest(calculated, received)
    except Exception:
        return False


def tg_user_id_from_init_data(init_data: str):
    try:
        pairs = dict(parse_qsl(init_data, keep_blank_values=True))
        return (json.loads(pairs.get("user", "")) or {}).get("id")
    except Exception:
        return None


_tg_admins_cache = {}    # chat_id -> (ts, {uid,...})
TG_ADMINS_TTL = 300      # список админов кэшируется на 5 минут


def tg_chat_admin_allowed(chat_id: int, init_data: str) -> bool:
    """Полный функционал игры — только админам группы именно этого чата."""
    if not BOT_TOKEN or BOT_TOKEN == "fake":
        return True                       # тестовый контур — проверка отключена
    uid = tg_user_id_from_init_data(init_data)
    if not uid:
        return False
    now = time.time()
    hit = _tg_admins_cache.get(chat_id)
    if hit and now - hit[0] < TG_ADMINS_TTL:
        return uid in hit[1]
    admins = None
    try:
        req = urllib.request.Request(
            f"https://api.telegram.org/bot{BOT_TOKEN}/getChatAdministrators?chat_id={chat_id}")
        result = json.load(urllib.request.urlopen(req, timeout=15)).get("result", [])
        admins = {m["user"]["id"] for m in result
                  if m.get("status") in ("creator", "administrator")
                  and (m.get("user") or {}).get("id")}
    except Exception as e:
        print(f"[paint_bot] getChatAdministrators chat={chat_id} ошибка: {e!r}", flush=True)
        if hit:                           # сбой Bot API — держим прошлый список
            return uid in hit[1]
        admins = set()
    _tg_admins_cache[chat_id] = (now, admins)
    return uid in admins

CHALLENGE_TTL_SECONDS = 120  # срок жизни вызова на дуэль
APP_URL = "https://paint-bot.onrender.com"  # публичный адрес этого сервиса (для WebApp)

# ---------- Состояние в памяти ----------

# Соло-игры против компьютера: {(chat_id, user_id): {"type", "secret", "attempts"}}
solo_games = {}

# Ожидающие вызовы на дуэль: {chat_id: {"challenger_id", "challenger_name", "opponent_id", "opponent_name", "job"}}
pending_challenges = {}

# Активные дуэли: {chat_id: {"players": {uid: {"name", "secret"|None}}, "order": [uid, uid],
#                           "turn": int, "attempts": {uid: int}}}
duels = {}

# Рисовалка (общий лист группы): {chat_id: {"image": bytes (PNG), "msg_id": int|None}}
paint_state = {}

# Очередь чатов, где обновилась картинка (их надо перерисовать в Telegram)
paint_update_queue = queue.Queue()

# География чата: {chat_id: {user_key: {"user", "name", "icon", "lat", "lon", "got", "read"}}}
# Хранится в GitHub-репозитории paint-bot-data (файл geo.json), чтобы переживать перезапуски.
geo_state = {}
# RLock, а не Lock: внутри обработчиков под этим замком вызываются
# save-функции, которые тоже берут geo_lock (тот же поток) — обычный Lock дал бы дедлок
geo_lock = threading.RLock()

# Письма между метками: {letter_id: {"id","chat","from","from_name","to","text",
#          "from_lat","from_lon","to_lat","to_lon","start_ts","arrived"}}
letters_state = {}

# Ванильный Вулкан Какашек: на каждый чат свой экземпляр.
# volcano: {chat_id: {"lat","lon","spawn_ts","used"}} — живёт 5 минут, спавн раз в час
# в случайной точке в радиусе 8000 км от Москвы (суше и море равнозначны).
# poops: {poop_id: {"id","chat","to","to_name","from_lat","from_lon","to_lat","to_lon",
#          "start_ts","arrived"}} — розовые какашки, летящие от вулкана к метке адресата.
volcano_state = {}
poops_state = {}

# Похотливый Кит (бывш. ПодводнаяЛодка): на каждый чат свой экземпляр.
# submarine: {chat_id: {"lat","lon","spawn_ts","used","next_spawn"}} — живёт 10 минут, спавн раз в час
# ТОЛЬКО в океанах (проверка по встроенной маске суши). Уведомления в чат о спавне НЕТ.
# gifts: {gift_id: {"id","chat","from","from_name","to","to_name","from_lat","from_lon","to_lat","to_lon",
#          "start_ts","arrived","arrived_ts","opened","picture"}} — подарки летят со скоростью какашек.
submarine_state = {}
gifts_state = {}

# Репозиторий для данных (не трогать main — иначе каждая запись будет триггерить автодеплой Render)
GEO_REPO = "dbosrsov-cyber/paint-bot-data"
GEO_FILE = "geo.json"
LETTERS_FILE = "letters.json"
VOLCANO_FILE = "volcano.json"
GEO_TOKEN_ENV = "GEO_GITHUB_TOKEN"  # токен добавляется в Render как переменная окружения

# Письмо летит по прямой: 100 км за 10 минут
LETTER_SPEED_KM_PER_MIN = 10.0
# ТЕСТОВОЕ ускорение (механизм оставлен на будущее): скорость для пар из LETTER_TEST_PAIRS.
# 2026-10-26 тестовая пара Sumai <-> ПМ снята — все летят на общей скорости 10 км/мин.
LETTER_TEST_SPEED_KM_PER_MIN = 500.0
LETTER_TEST_PAIRS = set()
# Письма, где отправитель ИЛИ адресат — из этого списка, летят в N раз быстрее
# базовой скорости (Андрюха — далеко, США; 2.0 = 200 км за 10 мин)
LETTER_FAST_SENDERS = {}   # 2026-11-01: у Андрюхи обычная скорость (метка переехала ближе)
LETTER_MAX_TEXT = 500
LETTER_READ_KEEP_SEC = 86400  # прочитанное письмо можно перечитывать сутки, потом удаляется
# УДАЛЕНИЕ ЧАСТИЧНО ОТКЛЮЧЕНО (2026-10-26, по просьбе владельца): прочитанные письма
# с 2026-10-29 снова удаляются автоматически через сутки после прочтения (фоновый тик /geodata).
# Этот флаг глушит ТОЛЬКО удаление писем В ПУТИ при сносе адресной метки — оно по-прежнему выключено.
LETTERS_NEVER_DELETE = True

# ---------- Ванильный Вулкан Какашек ----------
VOLCANO_LIFETIME_SEC = 300       # вулкан на карте ровно 5 минут
VOLCANO_PERIOD_SEC = 3600        # перерыв между спавнами — час
VOLCANO_RADIUS_KM = 8000         # от Москвы (суше и море равнозначны)
MOSCOW_LAT, MOSCOW_LON = 55.7558, 37.6173
POOP_SPEED_KM_PER_MIN = LETTER_SPEED_KM_PER_MIN * 2.0  # какашки летят вдвое быстрее писем
POOP_ARRIVED_TTL_SEC = 300  # прибывшая какашка исчезает с карты через 5 минут (счётчик остаётся)

# ---------- Похотливый Кит: событие в океане и подарки ----------
SUBMARINE_LIFETIME_SEC = 600   # кит на карте ровно 10 минут
SUBMARINE_PERIOD_SEC = 3600    # перерыв между спавнами — час (+ случайные 0–50 мин)
SUBMARINE_FILE = "submarine.json"
GIFT_SPEED_KM_PER_MIN = 50.0   # подарок летит 500 км за 10 минут (быстрее какашек в 2.5 раза)
# «картинки» подарков: смешные эмодзи-композиции (18+), выпадают при открытии
GIFT_PICS = ["🍆💦", "🍑🔥", "🥵💋", "🍌😏", "🫦🌶️", "👅🍭", "🔞🐱", "🛏️😈", "💋🍓", "🍒👀"]

# ---------- Остров: покупка за ЗП, гости на самолёте, постройки ----------
# islands: {"chat_id|user": {"chat","owner","owner_name","lat","lon","name",
#          "xp","visits","buildings":[id...], "poop_day","poop_today","created_ts",
#          "guest": None | {"user","name","leg","from_lat","from_lon","to_lat","to_lon",
#                           "start_ts","souvenir"}}}
# leg: "to_guest" (самолёт летит ЗА гостем) -> "to_island" (гостя везут на остров) ->
#      "staying" (гость на острове, самолёта на карте нет) -> "home" (улетает домой) -> None
islands_state = {}
ISLAND_FILE = "islands.json"
ISLAND_COST_ZP = 10             # стоимость острова, единиц ЗвезднойПыли
ISLAND_MAX_LEVEL = 10
ISLAND_XP_PER_LEVEL = 3         # уровень = 1 + xp // 3 (замок — с 21 опыта)
ISLAND_POOP_PER_DAY = 5         # какашек-удобрений в сутки на остров (1 какашка = +1 опыт)
ISLAND_STORM_PERIOD_SEC = 7200  # шторм примерно раз в 2 часа, в случайный момент окна
ISLAND_STORM_LIVE_SEC = 900     # дерево на берегу: 15 минут, потом волна уносит
ISLAND_STORM_WOOD = 2           # сколько дерева даёт один сбор
PLANE_SPEED_KM_PER_MIN = 300.0  # самолёт: 3000 км за 10 минут
# Бета Песочницы (ГеографияЧата 2.0): там все объекты летят 1000 км за 10 секунд
SANDBOX_FAST_KM_PER_MIN = 6000.0  # 1000 км / 10 сек
# сувениры за визит на остров — нейтральные эмодзи, добавляются в инфо метки гостя (видят все)
SOUVENIR_PICS = ["🍹", "🐚", "🏖️", "🥥", "🕶️", "🦀", "🌺", "🍍"]
# постройки: id -> (эмодзи, название, нужный уровень острова, цена ЗП, цена какашек)
ISLAND_BUILDINGS = {
    "hut":    ("🛖", "Хижина",           2, 5,  0),
    "bar":    ("🏖️", "Пляжный бар",       3, 10, 0),
    "statue": ("🗿", "Статуя Какашки",    5, 15, 10),
    "castle": ("🏰", "Островной замок",   8, 30, 0),
    "shipyard": ("⚓", "Верфь",           3, 0,  0, 30),
}
# имя острова генерируется автоматически, шутливо, обязательно с ником владельца {name}
ISLAND_NAME_TEMPLATES = [
    "Остров Обетованных Какашек {name}",
    "Необитаемый остров {name} (пока что)",
    "{name}ляндия",
    "Остров Отчаяния и {name}",
    "Республика Островов {name}",
    "{name} и Пальмы: вечная история",
    "Остров Грёз имени {name}",
    "Какашечные Гавайи {name}",
    "Заповедник «{name} и обезьяны»",
    "Остров {name}: здесь можно всё",
]

# Статистика: {user_id: {"games", "wins", "best"}}
stats = {}

# Известные пользователи (для разрешения @username в id): {username_lower: user_id}
users_by_name = {}

# Доступ: бот работает только в этих группах (личка всегда разрешена)
ALLOWED_GROUPS = {-1004400745434, -1002304715333}
GEO2_CHAT_ID = -1004400745434  # «ГеографияЧата 2.0» — пока только Песочница
WEEKLY_STATS_CHAT = -1002304715333  # «Другое измерение»: сюда пятница 16:00 МСК — итоги недели
ADMIN_ID = 8668538137  # кому сообщать о добавлении в чужие группы


def chat_allowed(chat) -> bool:
    """Личка — всегда можно; группа/канал — только из белого списка ALLOWED_GROUPS."""
    if chat.type in ("group", "supergroup", "channel"):
        return chat.id in ALLOWED_GROUPS
    return True


# ---------- География чата: сохранение меток в GitHub ----------

def geo_token() -> str:
    return os.environ.get(GEO_TOKEN_ENV, "").strip()


def geo_github_request(method: str, filename: str, extra_headers: dict | None = None) -> urllib.request.Request:
    headers = {
        "Authorization": f"Bearer {geo_token()}",
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
    }
    headers.update(extra_headers or {})
    return urllib.request.Request(
        f"https://api.github.com/repos/{GEO_REPO}/contents/{filename}", headers=headers, method=method
    )


def _save_json_to_github(filename: str, state: dict, lock: threading.Lock, label: str) -> bool:
    """Сохранить JSON в paint-bot-data. Вернуть True при успехе (для ретраев в бэкапе)."""
    if not geo_token():
        return False
    try:
        with lock:
            payload = json.dumps(state, ensure_ascii=False).encode("utf-8")
        body = {
            "message": f"{label}: update",
            "content": base64.b64encode(payload).decode("ascii"),
        }
        try:
            current = json.load(urllib.request.urlopen(geo_github_request("GET", filename), timeout=15))
            body["sha"] = current["sha"]
        except urllib.error.HTTPError as e:
            if e.code != 404:
                raise  # файл ещё не создан — пишем без sha
        req = geo_github_request("PUT", filename, {"Content-Type": "application/json"})
        req.data = json.dumps(body).encode("utf-8")
        urllib.request.urlopen(req, timeout=15)
        return True
    except Exception as e:
        print(f"[paint_bot] {label} save failed: {e!r}", flush=True)
        return False


def _load_json_from_github(filename: str, label: str):
    """Вернуть распарсенный JSON из файла репозитория; None, если файла нет/токена нет."""
    if not geo_token():
        return None
    try:
        data = json.load(urllib.request.urlopen(geo_github_request("GET", filename), timeout=15))
        return json.loads(base64.b64decode(data["content"]).decode("utf-8"))
    except urllib.error.HTTPError as e:
        if e.code != 404:
            print(f"[paint_bot] {label} load failed: {e!r}", flush=True)
        return None
    except Exception as e:
        print(f"[paint_bot] {label} load failed: {e!r}", flush=True)
        return None


def geo_save_to_github() -> None:
    _save_json_to_github(GEO_FILE, geo_state, geo_lock, "geo")


def geo_load_from_github() -> None:
    if not geo_token():
        print("[paint_bot] GEO_GITHUB_TOKEN не задан — метки живут только в памяти", flush=True)
        return
    loaded = _load_json_from_github(GEO_FILE, "geo")
    if loaded is None:
        print("[paint_bot] geo: файла geo.json ещё нет — начинаем с чистого листа", flush=True)
        return
    geo_state.update({int(cid): markers for cid, markers in loaded.items()})
    total = sum(len(m) for m in geo_state.values())
    print(f"[paint_bot] geo: загружено {total} меток из Git", flush=True)


def letters_save_to_github() -> None:
    _save_json_to_github(LETTERS_FILE, letters_state, geo_lock, "letters")


def letters_load_from_github() -> None:
    loaded = _load_json_from_github(LETTERS_FILE, "letters")
    if loaded:
        letters_state.update(loaded)
        print(f"[paint_bot] letters: загружено {len(loaded)} писем из Git", flush=True)


TGIDS_FILE = "tgids.json"
tgids_state = {}   # {chat_id(str): {tg_user_id(str): {"name": first_name, "uname": username, "ts": int}}}


def tgids_save_to_github() -> None:
    _save_json_to_github(TGIDS_FILE, tgids_state, geo_lock, "tgids")


def tgids_load_from_github() -> None:
    loaded = _load_json_from_github(TGIDS_FILE, "tgids")
    if loaded:
        tgids_state.update(loaded)
        total = sum(len(v) for v in tgids_state.values())
        print(f"[paint_bot] tgids: загружено {total} записей", flush=True)


_tgids_last_save = 0.0


def record_tgid(chat_id: int, user) -> None:
    """Запомнить Telegram ID автора сообщения — нужно для привязки ID к меткам на карте."""
    global _tgids_last_save
    if user is None or not chat_id:
        return
    ent = tgids_state.setdefault(str(chat_id), {}).setdefault(str(user.id), {})
    changed = (ent.get("name") != (user.first_name or "")
               or ent.get("uname") != (user.username or ""))
    ent["name"] = user.first_name or ""
    ent["uname"] = user.username or ""
    ent["ts"] = int(time.time())
    if changed and time.time() - _tgids_last_save > 60:
        _tgids_last_save = time.time()
        tgids_save_to_github()


def volcano_save_to_github() -> None:
    payload = {"volcanoes": {str(k): v for k, v in volcano_state.items()},
               "poops": poops_state}
    _save_json_to_github(VOLCANO_FILE, payload, geo_lock, "volcano")


def volcano_load_from_github() -> None:
    loaded = _load_json_from_github(VOLCANO_FILE, "volcano")
    if not loaded:
        return
    volcano_state.update({int(cid): v for cid, v in loaded.get("volcanoes", {}).items()})
    poops_state.update(loaded.get("poops", {}))
    print(f"[paint_bot] volcano: загружено вулканов {len(volcano_state)}, какашек {len(poops_state)}", flush=True)


# ---------- СагаЧата: анонимное коллективное сочинение ----------
# saga: {chat_id: {"chapters": [str, ...], "last_author": int|None, "started_ts": float}}
# Авторство нигде не хранится и не показывается: last_author — только чтобы
# запретить одному человеку писать две главы подряд.
saga_state = {}
SAGA_FILE = "saga.json"
SAGA_MAX_CHAPTERS = 30
SAGA_MIN_LEN = 30
SAGA_MAX_LEN = 280
SAGA_PREFIX = "saga"  # глава = сообщение «saga <текст>»
SAGA_NAG_SEC = 8 * 3600  # напоминание в чат, если 8ч никто не писал главу

SAGA_ZAGINS = [
    "В то утро в чате пропал последний спокойный человек, и никто даже не удивился.",
    "Андрюха поставил метку в океан, а утром метка ответила ему «привет».",
    "Старейшины чата собрались тайно и решили: пора начинать Сагу.",
    "Никто не знал, что бот мечтал стать писателем, пока он сам не начал эту историю.",
    "Письмо из географии прибыло пустым, а внутри оказалась только записка «начинайте».",
    "Ванильный Вулкан проснулся и прошептал историю, которую слышал от гор.",
    "Розовая Какашка приземлилась не в ту метку — и это перевернуло всё.",
    "На холсте рисовалки ночью проступили слова: «Продолжите за меня».",
    "Группа приняла правило: кто последний, тот начинает легенду. Оказалось, что последний — бот.",
    "Стая диких эмодзи животных перешла из карты прямо в текст чата.",
    "Одиннадцать быков и ни одной коровы: совпадение? История начинается.",
    "В чат добавили нового участника, но все поняли: участник добавил чат.",
]

SAGA_END_RE = re.compile(r"(конец|the end)[\.!\s…]*$", re.IGNORECASE)

# ---------- Метеорит и ресурс «ЗвезднаяПыль» ----------
# meteor: {chat_id: {"current": {"lat","lon","fall_ts","taken"} | None,
#                     "craters": [{"lat","lon","fall_ts","zp"}...],   # воронки навсегда
#                     "next_fall": float}}
# stardust: {"chat_id|user_key": int} — личный баланс звёздной пыли
meteor_state = {}
stardust_state = {}
meteor_credits = {}   # {tag: true} — выполненные разовые начисления (защита от повторов)
METEOR_FILE = "meteor.json"
METEOR_LIFETIME_SEC = 300     # 5 минут на сбор пыли из свежей воронки
METEOR_PERIOD_SEC = 3600      # перерыв между падениями — час (+ случайные 0–50 мин)
LETTER_BOOST_KM = 1000        # ускорение: мгновенное продвижение письма на 1000 км, стакается

METEOR_NOTIFY_TEXT = ("☄️ МЕТЕОРИТ! На карту чата упал метеорит — спеши собрать "
                      "ресурс ЗвезднаяПыль! Открой карту, найди воронку 💥 и жми "
                      "«Забрать ЗП» — кто первый, тому и пыль. Пыль нужна, чтобы "
                      "ускорять письма ✉️⏩")


# Привязки Telegram-ID к существующим меткам: (chat_id, старый ключ, новый ключ = tg id).
# Одноразовая миграция при старте: переименовывает ключ метки и все ссылки на него.
MARKER_TG_BINDINGS = [
    (-1002304715333, "Вита", "58334278"),
]

# Привязка числового id Telegram к метке БЕЗ переименования ключа:
# ключи меток трогать нельзя — фронтенд сравнивает myKey() напрямую.
# Сервер узнаёт игрока по tid (см. resolve_marker_key / viewer_matches).
# Собрано из tgids.json 2026-11-04, подтверждено Sumai. Apollo — ждём его сообщения.
TID_BINDINGS = [
    (-1002304715333, "Gaya", "8634767211"),
    (-1002304715333, "Ice", "712405567"),
    (-1002304715333, "Apollo", "8426689700"),
    (-1002304715333, "Макс", "521799467"),
    (-1002304715333, "Leon", "7889362443"),
    (-1002304715333, "Sofifa", "179490526"),
    (-1002304715333, "Sumai", "8668538137"),
    (-1002304715333, "anon", "1872544611"),
    (-1002304715333, "Андрюха", "8584582199"),
    (-1002304715333, "Мари", "8922818457"),
    (-1002304715333, "ПМ", "769828689"),
    (-1002304715333, "Снежанна", "1687254754"),
    (-1002304715333, "Татев", "7771949205"),
    (-1002304715333, "Юлия", "1217843099"),
    # Песочница (GEO2): те же подтверждённые id, иначе WebApp не узнаёт игроков
    (-1004400745434, "Sumai", "8668538137"),
]


def apply_tid_bindings() -> None:
    """Проставить tid на метки по подтверждённому списку (вызывается при старте)."""
    applied = 0
    for chat_id, marker_key, tid in TID_BINDINGS:
        marker = geo_state.get(chat_id, {}).get(marker_key)
        if marker is None:
            print(f"[paint_bot] tid_bind: метка {marker_key!r} не найдена (чат {chat_id})", flush=True)
            continue
        if str(marker.get("tid", "")) == str(tid):
            continue
        marker["tid"] = str(tid)
        applied += 1
        print(f"[paint_bot] tid_bind: {marker_key!r} -> tid {tid}", flush=True)
    if applied:
        geo_save_to_github()
        print(f"[paint_bot] tid_bind: применено привязок {applied}", flush=True)


def apply_remove_tid_dup_markers() -> None:
    """Удалить метки-двойники: ключ-метки = числовой tid, который уже есть у ДРУГОЙ
    метки этого чата (клиент когда-то поставил метку по ключу-тиду, не будучи узнан).
    Метки типа Виты (key == tid и дубля нет) не трогаем."""
    removed = 0
    for cid, markers in list(geo_state.items()):
        tid2key = {}
        for k, m in markers.items():
            t = str(m.get("tid") or "")
            if t:
                tid2key.setdefault(t, k)
        for k in list(markers.keys()):
            if str(k).isdigit() and str(k) in tid2key and tid2key[str(k)] != k:
                del markers[k]
                removed += 1
                print(f"[paint_bot] dup-метка удалена: chat={cid} key={k} (канон: {tid2key[str(k)]})", flush=True)
    if removed:
        geo_save_to_github()
        print(f"[paint_bot] удалено дублей-меток: {removed}", flush=True)


def apply_marker_bindings() -> None:
    for chat_id, old_key, new_key in MARKER_TG_BINDINGS:
        tag = f"bind_marker_{chat_id}_{old_key}_{new_key}"
        if meteor_credits.get(tag):
            continue
        markers = geo_state.get(chat_id, {})
        marker = markers.get(old_key)
        if marker is not None:
            markers[new_key] = markers.pop(old_key)
            marker["user"] = new_key
            for letter in letters_state.values():
                if letter.get("chat") != chat_id:
                    continue
                if letter.get("from") == old_key:
                    letter["from"] = new_key
                if letter.get("to") == old_key:
                    letter["to"] = new_key
            for poop in poops_state.values():
                if poop.get("chat") == chat_id and poop.get("to") == old_key:
                    poop["to"] = new_key
            for gift in gifts_state.values():
                if gift.get("chat") != chat_id:
                    continue
                if gift.get("from") == old_key:
                    gift["from"] = new_key
                if gift.get("to") == old_key:
                    gift["to"] = new_key
            for isl in islands_state.values():
                if isl.get("chat") != chat_id:
                    continue
                if isl.get("owner") == old_key:
                    isl["owner"] = new_key
                owners = isl.get("owners")
                if owners and old_key in owners:
                    isl["owners"] = [new_key if o == old_key else o for o in owners]
                guest = isl.get("guest")
                if guest and guest.get("user") == old_key:
                    guest["user"] = new_key
            skey_old = f"{chat_id}|{old_key}"
            if skey_old in stardust_state:
                skey_new = f"{chat_id}|{new_key}"
                merged = stardust_state.pop(skey_old) + stardust_state.get(skey_new, 0)
                stardust_state[skey_new] = merged
            geo_save_to_github()
            letters_save_to_github()
            volcano_save_to_github()
            meteor_save_to_github()
            submarine_save_to_github()
            islands_save_to_github()
            logline(f"marker binding applied: chat={chat_id} {old_key} -> {new_key}")
        meteor_credits[tag] = True
        meteor_save_to_github()


def _stamp_tid(marker: dict, viewer: str) -> None:
    """Запомнить числовой id Telegram на метке — тогда смена ника в Telegram
    ничего не сломает: метка находится по id. Сохраняет geo.json (вызывать под geo_lock
    или без него — geo_lock RLock)."""
    if not str(viewer).isdigit() or marker.get("tid"):
        return
    marker["tid"] = viewer
    geo_save_to_github()


def viewer_matches(recipient: str, viewer: str, name: str, chat_id: int) -> bool:
    """Зритель == адресат? Ключ метки может отличаться от ключа Telegram WebApp
    (метки ставили и из браузера — по имени), поэтому совпадаем по имени метки
    и по запомненному числовому id Telegram (tid) — ник может смениться, id — нет."""
    if recipient == viewer:
        return True
    marker = geo_state.get(chat_id, {}).get(recipient)
    if not marker:
        return False
    if viewer and str(marker.get("tid", "")) == str(viewer):
        return True
    if not name:
        return False
    mn = str(marker.get("name", ""))
    plain = str(name).lstrip("@")
    if mn and (mn == name or mn == plain or ("@" + mn) == name):
        _stamp_tid(marker, viewer)
        return True
    return False


def resolve_marker_key(chat_id: int, user: str, name: str) -> str | None:
    """Ключ метки пользователя: точно по ключу, по запомненному id Telegram (tid),
    иначе по имени (метки ставили из браузера — ключ = имя). При совпадении по имени
    запоминает числовой id на метке — смена ника в Telegram ничего не сломает."""
    markers = geo_state.get(chat_id, {})
    if user in markers:
        marker = markers[user]
        if not marker.get("tid"):
            _stamp_tid(marker, user)
        return user
    for k, m in markers.items():
        if user and str(m.get("tid", "")) == str(user):
            return k
    if name:
        plain = str(name).lstrip("@")
        for k, m in markers.items():
            mn = str(m.get("name", ""))
            if mn and (mn == name or mn == plain or ("@" + mn) == name):
                _stamp_tid(m, user)
                return k
    return None


def _stamp_ship_tid(ship: dict, user: str) -> None:
    """Запомнить числовой id Telegram на касатке (сохранение — в вызывающем хендлере)."""
    if str(user).isdigit() and not ship.get("tid"):
        ship["tid"] = user


def resolve_ship_key(ships: dict, user: str, name: str) -> str | None:
    """Ключ касатки игрока: точно по ключу, по запомненному id (tid), иначе по имени.
    При совпадении по имени запоминает числовой id — смена ника ничего не сломает."""
    if user in ships:
        _stamp_ship_tid(ships[user], user)
        return user
    for k, sh in ships.items():
        if user and str(sh.get("tid", "")) == str(user):
            return k
    if name:
        plain = str(name).lstrip("@")
        for k, sh in ships.items():
            sn = str(sh.get("name", ""))
            if sn and (sn == name or sn == plain or ("@" + sn) == name):
                _stamp_ship_tid(sh, user)
                return k
    return None


def meteor_save_to_github() -> None:
    payload = {"meteors": {str(k): v for k, v in meteor_state.items()},
               "stardust": stardust_state,
               "credits": meteor_credits}
    _save_json_to_github(METEOR_FILE, payload, geo_lock, "meteor")


def meteor_load_from_github() -> None:
    loaded = _load_json_from_github(METEOR_FILE, "meteor")
    if not loaded:
        return
    meteor_state.update({int(cid): m for cid, m in loaded.get("meteors", {}).items()})
    # воронки больше не храним: чистим сохранённые при загрузке и перезаписываем файл
    for _m in meteor_state.values():
        if _m.get("craters"):
            _m["craters"] = []
    meteor_save_to_github()
    stardust_state.update(loaded.get("stardust", {}))
    meteor_credits.update(loaded.get("credits", {}))
    apply_startup_credits()
    meteor_cleanup_craters()
    print(f"[paint_bot] meteor: чатов {len(meteor_state)}, балансов пыли {len(stardust_state)}", flush=True)


# Разовые начисления ЗП при старте: (chat_id, user_key, amount, tag)
# tag хранится в meteor.json — начисление сработает ровно один раз.
STARTUP_CREDITS = [
    (-1004400745434, "Sumai", 100, "sandbox_sumai_100zp_2026-11-01"),
]

# Разовые выдачи ресурсов (дерево/какашки на метку + ЗП) — применяются при старте,
# тег в meteor_credits защищает от повторов.
SANDBOX_GRANTS = [   # (chat, user, wood, poops, zp, tag)
    (-1004400745434, "Sumai", 100, 100, 100, "sandbox_grant_v2_sumai"),
    (-1004400745434, "test2", 100, 100, 100, "sandbox_grant_v2_test2"),
    (-1004400745434, "test3", 100, 100, 100, "sandbox_grant_v2_test3"),
]


def apply_sandbox_grants() -> None:
    for chat_id, user, wood, poops, zp, tag in SANDBOX_GRANTS:
        if meteor_credits.get(tag):
            continue
        marker = geo_state.get(chat_id, {}).get(user)
        if marker is not None:
            marker["wood"] = marker.get("wood", 0) + wood
            marker["poops"] = marker.get("poops", 0) + poops
        skey = f"{chat_id}|{user}"
        stardust_state[skey] = stardust_state.get(skey, 0) + zp
        meteor_credits[tag] = True
        logline(f"sandbox grant applied: {skey} +{wood} дерева +{poops} какашек +{zp} ЗП (tag {tag})")
    geo_save_to_github()
    meteor_save_to_github()


def apply_sandbox_island_levels() -> None:
    """Разовая выдача: всем островам Песочницы — 10 уровень (xp=27, уровень=1+xp//3)."""
    tag = "sandbox_islands_lvl10_xp_2026-11-04"
    if meteor_credits.get(tag):
        return
    changed = False
    for isl in islands_state.values():
        if isl.get("chat") == -1004400745434 and isl.get("xp", 0) < 27:
            isl["xp"] = 27
            isl.pop("level", None)   # поля level в данных нет — уровень считается из xp
            changed = True
            logline(f"sandbox island xp->27: {isl.get('name', isl.get('owner'))}")
    meteor_credits[tag] = True
    if changed:
        islands_save_to_github()
    meteor_save_to_github()

def apply_sumai_wreck_east6000() -> None:
    """Разовая телепортация: крайний левый (западный) мемориальный риф Sumai
    на 6000 км восточнее текущей точки."""
    tag = "sumai_wreck_east6000_2026-11-05"
    if meteor_credits.get(tag):
        return
    meteor_credits[tag] = True
    wr = wrecks_state.get("-1002304715333|Sumai|1793821487")
    if wr is not None:
        dlon = 6000.0 / (111.32 * max(math.cos(math.radians(wr["lat"])), 0.1))
        wr["lon"] = round(wr["lon"] + dlon, 6)
        wrecks_save_to_github()
        logline(f"wreck Sumai east 6000 km -> lon {wr['lon']}")
    meteor_save_to_github()

def apply_ship_teleport_sumai() -> None:
    """Разовая телепортация: потопленный Галеон Sumai ровно на 10000 км западнее
    точки боя (убрать наложение на корабль ПМ). Координаты абсолютные."""
    tag = "ship_sumai_west10000_abs_2026-11-04"
    if meteor_credits.get(tag):
        return
    meteor_credits[tag] = True
    sh = ships_state.get(ship_key(-1002304715333, "Sumai"))
    if sh is not None and sh.get("sunk"):
        base_lat, base_lon = -53.60186060396411, 65.87886000454296   # точка боя
        dlon = 10000.0 / (111.32 * max(math.cos(math.radians(base_lat)), 0.1))
        sh["lat"], sh["lon"] = base_lat, round(base_lon - dlon, 6)
        sh["to_lat"] = sh["to_lon"] = None
        sh["nav_from_lat"] = sh["nav_from_lon"] = None
        sh["route"] = None
        ships_save_to_github()
        logline(f"ship Sumai wreck moved west 10000 km -> lon {sh['lon']}")
    meteor_save_to_github()


def apply_ship_teleport_sumai_random_ocean() -> None:
    """Разовая телепортация (2026-11-08): Галеон Sumai застрял между островами
    у Гренландии (79.27, -70.57) — переносим в случайную точку открытого океана."""
    tag = "ship_sumai_random_ocean_2026-11-08"
    if meteor_credits.get(tag):
        return
    meteor_credits[tag] = True
    sh = ships_state.get(ship_key(-1002304715333, "Sumai"))
    if sh is not None and not sh.get("sunk"):
        lat, lon = 25.0, -40.0   # запасная середина Атлантики
        for _ in range(200):
            cand_lat, cand_lon = sifa_random_water(None)
            # только открытый океан: из точки должен существовать водный путь
            if ship_water_route(cand_lat, cand_lon, 0.0, -30.0):
                lat, lon = cand_lat, cand_lon
                break
        sh["lat"], sh["lon"] = round(lat, 6), round(lon, 6)
        sh["to_lat"] = sh["to_lon"] = None
        sh["nav_from_lat"] = sh["nav_from_lon"] = None
        sh["route"] = None
        ships_save_to_github()
        logline(f"ship Sumai teleported to open ocean -> {sh['lat']}, {sh['lon']}")
    meteor_save_to_github()


def apply_free_ships_main() -> None:
    """Разовая выдача: каждому владельцу острова в «Другом измерении» — по Галеону,
    если живого корабля сейчас нет (потопленный не считается)."""
    tag = "free_ships_main_2026-11-04"
    if meteor_credits.get(tag):
        return
    meteor_credits[tag] = True
    given = 0
    for isl in islands_state.values():
        if isl.get("chat") != -1002304715333 or isl.get("banned"):
            continue
        owners = isl.get("owners") or [isl.get("owner")]
        if not owners:
            continue
        mkey = owners[0]
        old = ships_state.get(ship_key(-1002304715333, mkey))
        if old is not None and not old.get("sunk"):
            continue   # живой корабль уже есть
        ships_state[ship_key(-1002304715333, mkey)] = {
            "chat": -1002304715333, "user": mkey,
            "name": isl.get("owner_name") or mkey,
            "lat": isl["lat"], "lon": isl["lon"],
            "to_lat": None, "to_lon": None,
            "nav_from_lat": None, "nav_from_lon": None, "nav_ts": 0,
            "route": None,
            "sunk": False, "sunk_ts": 0, "wins": 0,
        }
        given += 1
        logline(f"free ship given to {mkey}")
    if given:
        ships_save_to_github()
    meteor_save_to_github()


def apply_restore_wrecks() -> None:
    """Разовая выдача: вернуть на карту два потопленных ранее Галеона
    (Sumai — на 10000 км западнее точки боя; Андрюха — где погиб)."""
    tag = "restore_wrecks_2026-11-04"
    if meteor_credits.get(tag):
        return
    meteor_credits[tag] = True
    chat = -1002304715333
    base_lat, base_lon = -53.60186060396411, 65.87886000454296   # точка боя Sumai
    dlon = 10000.0 / (111.32 * max(math.cos(math.radians(base_lat)), 0.1))
    wrecks_state[f"{chat}|Sumai|1793821487"] = {
        "chat": chat, "user": "Sumai", "name": "Sumai",
        "lat": base_lat, "lon": round(base_lon - dlon, 6),
        "sunk": True, "sunk_ts": 1793821487, "wins": 0,
    }
    wrecks_state[f"{chat}|Андрюха|1793825400"] = {
        "chat": chat, "user": "Андрюха", "name": "Андрюха",
        "lat": -40.4945325413781, "lon": 130.78125000000003,
        "sunk": True, "sunk_ts": 1793825400, "wins": 0,
    }
    wrecks_save_to_github()
    meteor_save_to_github()
    logline("wrecks restored: Sumai (10000 km west), Андрюха (place of death)")


def apply_fix_mari_pm_duel() -> None:
    """Разовый откат некорректного абордажа Мари vs ПМ (баг «3 раунда вместо 3 побед»):
    у Мари убрать лишнюю победу (3→2), у ПМ обнулить потерю корабля,
    убрать риф потопленного корабля ПМ с карты."""
    tag = "fix_mari_pm_duel_2026-11-05"
    if meteor_credits.get(tag):
        return
    meteor_credits[tag] = True
    chat = -1002304715333
    changed = False
    sh = ships_state.get(ship_key(chat, "Мари"))
    if sh is not None and sh.get("wins", 0) == 3:
        sh["wins"] = 2
        changed = True
        logline("fix duel: Мари wins 3->2")
    pm = geo_state.get(chat, {}).get("ПМ")
    if pm is not None and pm.get("ships_lost"):
        pm["ships_lost"] = 0
        changed = True
        logline("fix duel: ПМ ships_lost -> 0")
    wreck_key = f"{chat}|ПМ|1793872934"
    if wreck_key in wrecks_state:
        wrecks_state.pop(wreck_key, None)
        changed = True
        logline("fix duel: риф ПМ убран с карты")
    if changed:
        ships_save_to_github()
        geo_save_to_github()
        wrecks_save_to_github()
    meteor_save_to_github()


def apply_pm_ship_wins() -> None:
    """Разовое начисление: текущему живому кораблю ПМ +2 победы —
    раунды, выигранные в некорректно завершившемся абордаже с Мари."""
    tag = "pm_ship_wins2_2026-11-05"
    if meteor_credits.get(tag):
        return
    meteor_credits[tag] = True
    sh = ships_state.get(ship_key(-1002304715333, "ПМ"))
    if sh is not None and not sh.get("sunk"):
        sh["wins"] = sh.get("wins", 0) + 2
        ships_save_to_github()
        logline(f"fix duel: кораблю ПМ начислено +2 победы (итого {sh['wins']})")
    meteor_save_to_github()


def apply_gaya_lyubertsy() -> None:
    """Разовый перенос: метка Gaya — в район Люберец (Московская область)."""
    tag = "gaya_lyubertsy_2026-11-05"
    if meteor_credits.get(tag):
        return
    meteor_credits[tag] = True
    gaya = geo_state.get(-1002304715333, {}).get("Gaya")
    if gaya is not None:
        gaya["lat"], gaya["lon"] = 55.6783, 37.8846
        geo_save_to_github()
        logline("Gaya moved -> Люберцы (55.6783, 37.8846)")
    meteor_save_to_github()


def apply_anon_rename_dasha() -> None:
    """Разовое переименование: аккаунт anon (Владивосток) получает имя Даша —
    чтобы запасной профиль больше не выглядел общим и на него не попадали."""
    tag = "anon_rename_dasha_2026-11-05"
    if meteor_credits.get(tag):
        return
    meteor_credits[tag] = True
    anon = geo_state.get(-1002304715333, {}).get("anon")
    if anon is not None and anon.get("name") != "Даша":
        anon["name"] = "Даша"
        geo_save_to_github()
        logline("anon renamed -> Даша")
    meteor_save_to_github()


def apply_tatev_coowner() -> None:
    """Разовое: Татев — совладелец острова Андрюхи (равные права, как ПМ у Sumai)."""
    tag = "tatev_coowner_2026-11-08"
    if meteor_credits.get(tag):
        return
    meteor_credits[tag] = True
    isl = islands_state.get("-1002304715333|Андрюха")
    if isl is not None:
        owners = isl.setdefault("owners", [isl.get("owner", "Андрюха")])
        if "Татев" not in owners:
            owners.append("Татев")
            islands_save_to_github()
            logline("island Андрюха: совладелец Татев добавлен")
    meteor_save_to_github()


def apply_andrey_island_rename() -> None:
    """Разовое: переименование острова Андрюхи."""
    tag = "andrey_island_rename_2026-11-08"
    if meteor_credits.get(tag):
        return
    meteor_credits[tag] = True
    isl = islands_state.get("-1002304715333|Андрюха")
    if isl is not None and isl.get("name") != "Остров распутных девственниц":
        isl["name"] = "Остров распутных девственниц"
        islands_save_to_github()
        logline("island Андрюха renamed -> Остров распутных девственниц")
    meteor_save_to_github()


def apply_startup_credits() -> None:
    for chat_id, user, amount, tag in STARTUP_CREDITS:
        if meteor_credits.get(tag):
            continue
        key = f"{chat_id}|{user}"
        stardust_state[key] = stardust_state.get(key, 0) + amount
        meteor_credits[tag] = True
        meteor_save_to_github()
        logline(f"startup credit applied: {key} +{amount} ЗП (tag {tag})")


# Чаты, где воронки метеоритов не копятся: чистим при каждом старте бота
METEOR_CRATER_CLEANUP_CHATS = (-1002304715333,)   # «Другое измерение»


def meteor_cleanup_craters() -> None:
    # Только в окне воскресной задачи (вс 01:00–06:00 МСК). При каждом старте бота
    # чистить нельзя: Render перезапускает сервис при деплоях и простое — воронки
    # стирались бы по несколько раз в день вместо раза в неделю.
    now_msk = datetime.datetime.now(MSK_TZ)
    if now_msk.weekday() != 6 or not (1 <= now_msk.hour < 6):
        print(f"[paint_bot] meteor: уборка воронок пропущена (сейчас {now_msk.strftime('%a %H:%M')} МСК, окно — вс 01:00-06:00)", flush=True)
        return
    for cid in METEOR_CRATER_CLEANUP_CHATS:
        m = meteor_state.get(cid)
        if m and m.get("craters"):
            removed = len(m["craters"])
            m["craters"] = []
            meteor_save_to_github()
            logline(f"meteor craters cleaned chat={cid} removed={removed}")


# ---------- СИФА: догонялки на кораблях (прототип в ГЕО2) ----------
SIFA_FILE = "sifa.json"
SIFA_SAVE_INTERVAL_SEC = 10   # не чаще одного сохранения в Git
# --- догонялки «Сифа» ---
SIFA_PRESS_KM = 1500.0        # один ход «Плыть» — 1500 км за 10 сек
SIFA_PRESS_SEC = 10.0
SIFA_MOTOR_MULT = 3.0         # МоторV8: 4500 км за 10 сек
SIFA_PASS_KM = 1000.0         # ближе 1000 км — Сифа передана
SIFA_FROZEN_SEC = 600         # принявший Сифу неподвижен 10 минут
SIFA_MOTOR_SEC = 600          # МоторV8 работает 10 минут
SIFA_MAX_JUMP_KM = 250.0      # антителепорт: лимит скачка за один пакет
SIFA_LOG_PERIOD_SEC = 10800     # плывущее бревно появляется раз в 3 часа
SIFA_LOG_PICK_KM = 100.0        # подплыл вплотную — бревно твоё
SIFA_ABSENT_SEC = 48 * 3600     # касатка неактивного 48ч игрока удаляется (молча)
SIFA_ROTATE_SEC = 8 * 3600      # Сифа случайно переходит к другой живой касатке
SIFA_AREA_ADMINS = ("Sumai", "769828689", "8668538137")  # кто задаёт границы игры
SIFA_LAND_MASK_B64 = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//3/////////+QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/3/9////8GAAAAAAAAAAAB///////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////8AAAAAAAAAAP////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA8B//////////////gAAAAAB/4f////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////////////wAP//mD///////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////////////3/////////////////////////+B4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////////////////////////////////////D8D//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH8Af4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////////////9///////////////////////////n/////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/+A/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHAAB//8Af/4AAAAAAAAAAAAAAAB/AA/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//3////////////////////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfgA///9/j/8AAAAAAAAH8AAAAAD/j//4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///7///////////////////////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//7/4B///////+AAAAAAAAP+AAAAAD/H///gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////////////////////////////////////////////////gAAAAAAAAAAAAAAAAAAAAB4B4AAAAAAAAAAAAAD////87///////8AAAAAAAAP8AAAAAB+////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMAP//////////////////+///////////////////////////////////4AAAAAAAAAAAAAAAAAAAAB//////AAAB4AAAAAAD////7////////wAAAAAAAAH4AAAAAAB////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/gf//////////////////B//////////////////////////////////wAAAAAAAAAAAAAAAAAAAAH///////gAB/8AAAAAAB////3//////wAAAAAAAAAAAAAAAAAAH/////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/wf/////////////////4A//////////////////////////////////gAAAAAAAAAAAAAAAAA//3P///////wAD/4AAAAAAAA/9/7+H///gAAAAAAAAAHAAAAAAAAAP/////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/wP/////////////////AAf////////////////////////////////4AAAAAAAAAAAAAAAAAB///////////gAB8AAAAAAAAADQfwAA/MfAAAAAAAAAAP8AAAAAAAAH//////A4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/wADgH////////////////8AAF////////////////////////////////wAAAAAAAAAAAAAAAAAB///////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH+AAAAAAAAB//////P9gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//8AAA///////////////gAB/////////////////////////////////4AAAAAAAAAAAAAAAAAAB//////////wH+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8AAAAAAAAAB////+//8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH+AAP///wP8P/////////////4Af//////////////////////////////////wAAAAAAAAAAAAAAAAAAD///////w/+HP/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//gAH///8f/8/////////////4P///////////////////////////////////wAAAAAAAAAAAAAAAAAAD///////+AAPv+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//wAD///+f/+f////////////4f//////////////////////////////////84AAAAAAAAAAAAAAAAAAB////////8AHEIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////3+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///wAB////P/+D////////////wf//////////////////////////////////x4AAAAAAAAAAAAAAAAAAAf/////v/+gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////v/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////gAe////n//+P/+f///////+AP///////////////////////////////////7gAAAAAAAAAAAAAAAAAADP///+H//8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///+H+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAR8f///AA/gP//D///A/g////////4AH///////////////////////////////////3wAAAAAAAAAAAAAAAAAAAB///8D//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/Af/8cAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//H//+AAfwH8+Af/+B/w///////gAAP////////////////////////////////////gAAAAAAAAAAAAAAAAAAAA///wH//8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOAAAAQAAH//+OAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///nP/8AAP4AAAAP/8A/z///////AAAH////////////////////////////////////AAAAAAAAAAAAAAAAAAAAAf//gD//AAAAAAAAAAAAAAAAAAAAAAAAAAAAP8AAAAAAAAAAAAAfAAAP4AAf////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///PwwB8AH8Af5wf/+D/////////AAAD////////////////////////////////////AAAAAAAAAAAAAAAAAAAAAP/8AABwAAAAAAAAAAAAAAAAAAAAAAAAAAAB//AAAAAAAAAAAAAOAAAf7AA///////1AAAAAAAAAAAAAAAAAAAAAAAB8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////4AP+AA/x//+/////////////gAAAP//////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAB/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///gAAAAAAAAAAAAAAAAP3j/////////gAAAAAAAAAAAAAAAAAAAAAAD+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////+Af/AA/////f////////////AAAAD/////////////////////////////////98AAAAAAAAAAAAAAAAAAAAAAH4AAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////gAAAAAAAAAAAAAAABP///////////4AAAAAAAAAAAAAAAAcAQAAAB8AGAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////4f/78/////h/////////v/+AAAAAP////////////////////////////////+cAAAAAAAAAAAAAAAAAAAAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////AAAAAAAAAAAAAAAD/////////////+AAAAAAAAAAAAAAAH/h/AAAAAAPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////+P//+/////mf///7AD////8AAAAAH/////////////////////////////////eAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////4AAAAAAAAAAAAAAH///////////////AAAAAAAAAAAAAAeP///+AAAAAHgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////+f//////w/////////4AAAAAAP4AAAP///////////////////////////tAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABP/////+AAAAAAAAAOAAAAP////////////////AAAAAAAAAAAAAA/f////+OfAADAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA3/////////9+//////8/////////wAAAAAAAAAAAAf///////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////4AAAAAAAAAAfAAB//////////////////AAAAAAAAAAAAAA/f/////f//4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfv/////////P/////+/////////gAAAAAAAAAAAAD///////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////gAAAAAAAAAAA/AAP/////////////////+AAAAAAAAAAAAAAe/////+f//8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////5/AD//P/+f////////gAAAAAAAAAAAAB///////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////AAAAAAAAAAAAAeAA//////////////////8AAAAAAAAAAAAAAAf////8P//8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/wAAP//////w+AA//n/+P////////AAAAAAAAAAAAAAf//////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAOAAAAAAAAAAAAAAAAAAAAAAAD///4AAAAAAAAAAAAAAAZ//////////////////8AAAAAAAAAAAAAAAP////wD//4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///7+AH//4AAAAAAAHx/+H///////8AAAAAAAAAAAAAAD/////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAfAAAAAAAAAAAAAAAAAAAAAAAH///gAAAAAAAAAAAAADY8//////////////////+AAAAAAAAAAAAAAYB/fDgAAH/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////gD/+AAAAAAA3/g////5///3/4AAAAAAAAAAAAAAH/////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAOAAAAAAAAAAAAAAAAAAAAAAA///+AAAAAAAAAAAAAAH8Y//////////////////8AAAAAADgAAAAAA+AA/uAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////+AAAAAD/gAH//w///+Af/wf8//AAAAAAAAAAAAAH/////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAEAAAAAAAAAAAAAAAAAAAAAAD///gAAAAAAAAAAAAAAf////////////////////8D8AAAAfwAAAAAAfAAf/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////AAAAAH/wAf//5////D///////8AAAAAAAAAAAACP///////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//8AAAAAAAD4AA/gAH/////////////////////////wAA//vwAAAAOAA//8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////AAAD//4A///5///+H////////AAAAAAAAAAAAAP///////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//4AAAAAAAH+AF/wAP/////////////////////////7AB////AAAAAAB//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////vw/H//4P///8///4P////////wAAAAAAAAAAAAH///////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///wAAAAAAAf/Af/gPP////////////////////////////////gAAAAAB//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////3//wf///+///gf////////4AAAAAAAAAAAAP//////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///AAAAAAAB//4/wGfv////////////////////////////////gAAAAAA3//gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////7//Af///+///A//////////AAAAAAAAAAAAf//////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//8AAAAAAAD//8f4P/n////////////////////////////////wAAAAAB////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////AP///+f/8B//////////gAAAAAAAAAAAP//////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//4AAAAAAAH//8D8///////////////////////////////////wAAAAAD//////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////gH///+f8AB//////////4AAAAAAAAAAAH//////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//gAAAAAAAH//8f////////////////////////////////////4AYAAAH///////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////wA///+f4AD//////////+YAAAAAAAAAAD//////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///gAAAAAAAP//4/////////////////////////////////////wA8AEAP///////gAAAAAAAAAAAAAAAAAAA/wAAAAAAAAAAAAAEAAAAAAAAAAAAAAAAAAAA///+P/////////4AA////+AD////////////4AAAAAAAAAH//////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///gAAAAAAB/////////////////////////////////////////4B////////////8AAAAAAAAAAAAAAAAAAH/8AAAAAAAAAAAAAfgAAAAAAAAAAAAAAAAAAAD//+H/////////8AAP////AD////////////8AAAAAAAAAD//////////////////////8AAAAAAAAMAAAAAAAAAAAAAAAAAAAAABAAAAAAAAAAAAAAAAA///wAAAAAAP/////////////////////////////////////////4D/////////////gAAAAAAAAAAAAAAAAA//+AAAAAAAAAAACB/+fwAAAAAAAAAAAAAAAAAAP/8B/////////4AAH4P//gB////////////+AAAAAAAAAB//////////////////////8AAAAAAAB+AAAAAAAAAAAAAAAAAAAAAf+/AAAAAAAAAAAAAAAf///AAAAAAf//////////////////////////////////////////n/////////////wf//+BgAAAAAAAAAAB//8AAAAAAAAAAAf////4AAAAAAAAAAAAAAAAAAH4AD//////////QDDwP//4A//////////////AAAAAAAAAP/////////////////////8AAAAAAAD+AAAAAAAAAAAAAAAAAAAH/////AAAAAAAAAAAAAAD///4AAAAAf/////////////////////////////////////////////////////////////7wAAAAAAAAAAB//4AAAAAAAAAAD///////+AAAAAAAAAAAAAOAADgAB//////////+HgAP//8Af/////////////4AAAAAAAAP///////////////////3/8AAAAAAAD8AAAAAAAAAAAAAAAAAAAP/////8AAAAAAAAAAAAAA///8wAAAA////8//////////////////////////////////////////////////////////wAAAAAAAAAAB/AAAAAAAAAAAB//////////+AAAAAAAAADMfgDAAAAH///////////wAH///AP/////////////+AAAAAAAAP/////////////////////+AAAAAAABAAAAAAAAAAAAAAAAAAH2//////+AAAAAAAAAAAAAAH//5+AAAA////8//////////////////////////////////////////////////////////gAAAAAAAAAAAgAAAAAAAAAAAD/////////////AAAAAAAf/f4HgAAAD///////////gAP///gD//////////////gAAAAAAAf/////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAP///////+QAAAAAAAAAAAAAAA0j/wAAAX///5/////////////////////////////////////////////////////////+AAAAD+H/ugwAAAAAAAAAAAAAf//////////////gwAAYf///8Pz/wAH//////////+APv///gA//////////////wAAAAAAAf/////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAB//////////AAAAAAAAAAAAAAAAB///gAP///5//////////////////////////////////////////////////////////kf4AH/P////AAAAAAAAAAAAA////////////////4AD9////////+AD//////////+Af////+AD/////////////wAAAAAAA//////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAf//////////wAAAAAAAAAOAAAAAA////Af///7//////////////////////////////////////////////////////////////////////gAAAAAAAAAAB////////////////+AP///////////B//////////+n//////OAD////////////4AAAAAAAf////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAO////////////+AAAAAAAA/4AAAAAH///+f///5////////////////////////////////////////////////////////////////P/////4wAAAAAAAAh//////////////////////////////////////////9///7////gD///N////////8AAAAAAAP/z//////////////////gAAAAAAAAAAAAAAAAAAAAAAAAD//////////////wAAAAAAB/8AHwADw////////5////////////////////////////////////////////////////////////////H//////+AAAAAAAB///////////////////////////////////////////z////////wD///D+f//////4AAAAAAAB/n/////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAP///////////////gAADAAB/8A/4Qf5////+f//+////////////////////////////////////////////////////////////////////////4AAAAAAD///////////////////////////////////////////33///////4H///B8D//////4AAAAAAAAP//////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////4AAH/8A/4//z////////////f///////////////////////////////////////////////////////////////////////+AAAAAAH//////////////////////////////////////////7zj//5////93//+A4D//////+AAAAAAAAf/////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAD////////////////+IAD/+Afv///////////////v////////////////////////////////////////////////////////////////////////AAAAAAH///////////////////////////////////v/9////xgB///////////8B8P///////+AAAAAAA//////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////+AB//gIf///////////////P/////////////////////////////////////////////////////////////////////////gAAAAD////////////////////////////////////////////////////7///8A4f////////QAAAAAA////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////wAf/w/////////////////H/////////////////////////////////////////////////////////////////////////wAAAAAH///////////////////////////////////////////////////7///+AAf////////8AAAAAB//////////////48AAAAAAAAAAAAAAAAAAAAAAAAAAAAfn/////////////////4A//z/////////////////f/////////////////////////////////////////////////////////////////////////4wAAAAA////////////////////////////////////////////////////////AAf/fP//////wAAAAB//////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMP/////////////////8B//n////////////////+////////////////////////////////////////////////////////////////////////////4AAAAP///////////////////////////////////////////////////////AAP+Af//////+AAAAD/////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////8B/8H////////////////w////////////////////////////////////////////////////////////////////////////+AAAAD//////////////////////////////////////////////////////+AAH8A////////gAAAB/////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////8Y///////////////////D/////////////////////////////////////////////////////////////////////////////AAAH///////////////////////////////////////////////////////8AAAAB////////wAAAA/////////////4AAAAAAHgAAB4wAAAAAAAAAAAAAAAAAH//////////////////9+P/////////////////+f/////////////////////////////////////////////////////////////////////////////+AB//H/////////////////////////////////////////////////////wAAAAf////////wAAAB/////////////wAAAAAAf4AbP/4AAAAAAAAAAAAAAAAAf//////////////////7///////////////////////////////////////////////////////////////////////////////////////////////////AH////////////////////////////////////////////////////////AAAAA/////////gAAAB/////////////AAAAAAA/+P///4AAAAAAAAAAAAAAAAA///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////B////////////////////////////////////////////////////////8AAAAA/////3///AAAAA////////////8AAAAAAB//////4AAAAAAAAAAAAAAAAD///////////////w//////////////////////////////////////////////////////////////////////////////////////////////////////+D////////////////////////////////////////////////////////8AAAOB/////x//8AAAAAf///////////gAAAAAAH///////AAAAAAAAAAAAAAAAH///////////////wAeP///////////////////////////////////////////////////////////////////////////////////////////////////wD//////////////////////////////////////////////////////v/4AAAf//////4f/wAAAAAf//////////+AAAAAAAP///////gAAAAAAAAAAAAAAAH///////////////mGAf/////////////////////////////////////////////////////////////////////////////////////////////5/////gB//////////////////////////////////////////////////////v/8AAB////////P/AAAAAAP/////////iwAAAAAAAH///////gAAAAAAAAAAAAAAA///////+Af///////fwf/////////////////////////////////////////////////////////////////////////////////////////////wAH//wAAH////////////////////////////////////////////////////////wAD////////7+AAAAAAB////////8AAAAAAAAAD///////gAAAAAAAAAAAAAAB///////4A//////////P/////////////////////////////////////////////////////////////////////////////////////////////gAD//gAAD/////////////////////////////////////////////////////f//4AH////////98AAAAAAA////////wAAAAAAAAAD///////AAAAAAAAAAAAAAAB///////wB///////+////////////////////////////////////////////////////////////////////////////////////////////////AAB//gAAB////////////////////////////////////////////////////+f//8AH////////+AAAAAAAA////////wAAAAAAAAAB//////+AAAAAAAAAAAAAAAD///////4D///////////////////////////////////////////////////////////////////////////////////////////////////////8AAAD/AAAA//+f////////////////////////////////////////////////5////wD//v//////AAAAAAAA////////gAAAAAAAAAAD/////wAAAAAAAAAAAAAAAP///////wP///////////////////////////////////////////////////////////////////////////////////////////////////////gAAAA8M4AAAAIP////////////////////////////////////////////////z////4D/AA//////gAAAAAAAf///////AAAAAAAAAAAH/////AAAAAAAAAAAAAAAOf///////h////////////////////////////////////////////////////////////////////////////////////////////////////////wAAAAAf/AAAAD/////////////////////////////////////////////////H//3/8H+AAf/////gAAAAAAAP///////gAAAAAAAAAAH////wAAAAAAAAAAAAAAA/////////D////////////////////////////////////////////////////////////////////////////////////////////////////////wAAAAAf/4AAfP////////////////////////////////////////////////AH//h/4P/AAH/////gAAAAAAAH///////AAAAAAAAAAAD9//+AAAAAAAAAAAAAAAB//////////////////////////////////////////////////////////////////////////////////////////////////////////////////8AAAAAf/8AA/////////////////////////////////////////////////+ADj+fzgP+AAB/////gAAAAAAAD//////+AAAAAAAAAAAAAP/AAAAAAAAAAAAAAAAH////////z/////////////////////////////////////////////////////////////////////////////////////////////////////////+AAAAAOf4AB/////////////////////////////////////////////////8AAD8/4AHwA8A/////AAAAAAAAB//////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///////+B/////////////////////////////////////////////////////////////////////////////////////////////////////////+AAAAAADAAD/////////////////////////////////////////////////4AABB/4HB/B+Af////AAAAAAAAA//////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////wD/////////////////////////////////////////////////////////////////////////////////////////////////////////+AAAAAAAAAH/////////////////////////////////////////////////gAAAD/wPj///4P///fgAAAAAAAAf/////AAAAAAAAAAAAAAAAAAAAAAB8AAAAAAAP////////gD/////////////////////////////////////////////////////////////////////////////////////////////////////////+AAAAAAAAAP////////////////////////////////////////////////8AAAAB/Af3///+Dj//vAAAAAAAAAP/////AAAAAAAAAAAAAAAAAAAAAAD+AAAAAAAf////////AB///////////////////////////////////////////////////////////////////////////////////////////////f/////////8AAAAAAAAA/////////////////////////////////////////////////wAAAAA8Af3////gA//+AAAAAAAAAH/////AAAAAAAAAAAAAAAAAAAAAAD8AAAAAAA////////+AB///////////////////////////////////////////////////////////////////////////////////////////////////////4AQAAAAAAAAB/////////////////////////////////////////////////gAAAAAAAfj////wAA//AAAAAAAAAD/////gAAAAAAAAAAAAAAAAAAAAAB+AAAAAAA////////+AA//////////////////////////////////////////////////////////////////////////////////////////////////////+AAAAAAAAAAAB/////////////////////////////////////////////////AAAAAAAAPB////8AAC/AAAAAAAAAB/////AAAAAAAAAAAAAAAAAAAAAAA8AAAAAAA////////8AA///////////////////////////////////////////////////////////////////////////////////////////+f/////////wAAAAAAAAAAAA////////////////////////////////////////////////4AAAAAAAACB/////8AAfAAAAAAAAAA////+AAAAAAAAAAAAAAAAAAAAAAAYAAAAAAB////////8AA//////////////////////////////////////////////////////////////////////////////////////////8AP/n//////8AAAAAAAAAAAAAP///////////////////////////////////////////////wAAAAAAAAAP/////+AAGAAAAAAAAAAf///8AAAAAAAAAAAAAAAAAAAAAAAAAAAYAAB////////8AB//////////////////////////////////////////////////////////////////////////////////////////4Af8P//////wAAAAAAAAHAAABn///////////////////////////////////////////////wAAAAAAAAAf/////+OADAAAAAAAAAAH///8AAAAAAAAAAAAAAAAAAAAAAAAAAB8AAA/////////gx//////////////////////////////////////////////////////////////////////////////////////////AAPx///////AAAAAAAAAPgAAf////////////////////////////////////////////////gAAAAAAAAAP/////8fAHgAAAAAAAAAD///4AAAAAAAAAAAAAAAAAAAAAAAAAAD4AAA/////////x5/////////////////////////////////////////////////////////////////////////////////////////+AADj//////8AAAAAAAAAHwAA/////////////////////////////////////////////////AAAAAAAAAEB/////+eAPgAAAAAAAAAAAf/wAAAAAAAAAAAAAAAAAAAAAAAAAAHwAAA//////////8/////////////////////////////////////////////////////////////////////////////////////////8AAAH//////AAAAAAAAAADgAAf/////////////4//////////////////////////////////AAAAAAAAAOA/////8MAfwAAAAAAAAAAAH/4AAAAAAAAAAAAAAAAAAAAAAAAAADwAAAf/////////+///wH////////////////////////////////////////////////////////////////////////////////////gAAA////wA+AAAAAAAAAAAAAAP8P///////n//+AP/////////////////////////////////AAAAAAAAAeB/////+AA/4AAAAAAAAAAAA/wAAAAAAAAAAAAAAAAAAAAAAAAAAAgAAA/////////+0Z////////////////////////////////////////////////////////////////////////////////////////wAAD///nAAcAAAAAAAAAAAAAADwHh//////P/wMAEAD///////////////////////////////AAAAAAAAAcD/////+AA/8AAAAAAAAAAAAGAAAAAAAAAAAAAAAAAAAAAAAAAADwAAAAf////////8AAf///////////////////////////////////////////////////////////////////////////////////////4AAP//HCAAAAAAAAAAAAAAAAAAAAD/////+P+AAAAAAD//////////////////////////////AAAAAAAAAIH//////gB//AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH4AAAAf////////4AH////////////////////////////////////////////////////////////////////////////////////4f//8AAf//+AAAAAAAAAAAAAAAAAAAAAD//////H4AAAAAAAf/////////////////////////////+AAAAAAAAAP//////wH//gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPwAAAAP////////4AP////////////////////////////////////////////////////////////////////////////////8A75w///4AAf///AAAAAAAAAAAAAAAAAAAAAH//////4AAAAAAAAH//////////////////////////////AAAAAAAAAP//////+f//wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAGH/gAAAAP//+f////wAP///////////////////////////////////////////////////////////////////////////////8AAAAAf/mAAB///+AAAAAAAAAAAAAAAAAAAAAD+f////8AAAAAAAAB//////////////////////////////gAAAAAAAAP//////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfP/gAAAAP//wf///8AAf///////////////////////////////////////////////////////////////////////////////4AAAAAAgAAAH//74AAAAAAAAAAAAAAAAAAAAAAkBr///+AAAAAAAAAf/////////////////////////////gAAAAAAAAH//////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/f/AAAAAH//Af///wOAf///////////////////////////////////////////////////////////////////////////////gAAAAAAAAAA///5gAAAAAAAAAAAAAAAAAAAAAAAAD///8AAAAAAAAAD/////////////////////////////wAAAAAAAAB//////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB+//8AAAAA/8BP///w/APz/////////////////////////////////////////////////////////////////////////////+AAAAAAAAAAP///+AAAAAAAAAAAAAAAAAAAAAAAAAH///4AAAAAAAAAD/////////////////////////////wAAAAAAACAP/////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///+AAAAAfwPn///h/APx/////////////////////////////////////////////////////////////////////////////+AAAAAAAAAAf////AAAAAAAAAAAAAAAAAcAAAAAAAf///8AAAAAAAAAB/////////////////////////////4eAAAAAAHAH//////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////AAAAAAB/7///x+Af4/////////////////////////////////////////////////////////////////////////////8AAAAAAAAAAP///+AAAAAAAAAAAAAAAAA+AAAAAAB//n/4AAAAAAAAAAf//////////////////////////////4AAAAACAD//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///+AAAAAAH/9///78A///////////////////////////////////////////////////////////////////////////////gAAAAAAAAAAf///8AAAAAAAAAAAAAAAAAfAAAAAAD/+D/gAAAAAAAAAAf//////////////////////////////+AAAAAHAD//////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///+AAAAAAP/4///54B///////////////////////////////////////////////////////////////////////////////AAAAAAAAAAB////+AAAAAAAAAAAAAAAAAHgAAAAA//8D/AAAAAAAAAAAP///////////////////////////////wAAAAP4D//////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABv//8AAAAAAf/w///wwD//////////////////////////////////////////////////////////////////////////////8AAAAAAAAAAD/////AAAAAAAAAAAAAAAAAHgAAAAB//wH4AAAAAAAAAAAD///////////////////////////////4AAAAH8D//////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//4AAAAAAf/4f//gAD//////////////////////////////////////////////////////////////////////////////wAAAAAAAAAAD/////AAAAAAAAAAAAAAAAADAAAAA//8ATwAAAAAAAAAAAB////////////////////////////////AAAAP8D//////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//4AAAAAA//////gAD//////////////////////////////////////////////////////////////////////////////gAAAAAAAAAAH/////AAAAAAAAAAAAAAAAAAAAAAD//4A4AAAAAAAAAAAAA////////////////////////////////+AAAP4P//////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//+AAAAAAf////9AAD/////////////////////////////////////////////////////////////////////////////+AAAAAAAAAAAH////+AAAAAAAAAAAAAAAAAAAAAAH//wB4AAAAAAAAAAAAAP////////////////////////////////gAAPwf///////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///AAAAAAf///+IAAD/////////////////////////////////////////////////////////////////////////////8AAAAAAAAAAAH////sAAAAAAAAAAAAAAAAAAAAAAf/8AAwAAAAAAAAAAAAAH//////////////////////////////////AHD////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////gAAAAAf////gAAD/////////////////////////////////////////////////////////////////////////////0AAAAAAAAAAAH////AAOAAAAAAAAAAAAAAAAAAAf//+AAAAAAAAAAAAAAAAH//////////////////////////////////gAf////////////+QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////gAAAAAP////wAAf//////////////////////////////////////////////////////////////////////////////gAAAAAAAAAAP////AAfAAAAAAAAAAAAAAAAAAA//T/AAAAAAAAAAAAAAAAD//////////////////////////////////wD//////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////gAAAAAf//7Hwf4///////////////////////////////////////////////////////////////////////////////wAAAAAAAAAAP////gAPnAAAAAAAAAAAAAAAAAB//A+AAAAAAAAAAAAAAAAA//////////////////////////////////wH//////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////8AAAAAf///jh/9///////////////////////////////////////////////////////////////////////////////gAAgAAAAAAAP////gAH/gAAAAAAAAAAAAAAAAf/+AAAAAAAAAAAAAAAAAAAbv////////////////////////////////wD//////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////+AAAAAP///w//////////////////////////////////////////////////////////////////////////////////PgDwAAAAAAAH////AADngAAAAAAAAAAAAAAAH/8MAAAAAAAAAAAAAAAAAAA/3////////////////////////////////gD//////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////AAAAAH//////////////////////////////////////////////////////////////////////////////////////f4H4AAAAAAAD///+AAABAAAAAAAAAAAAAAAAP8AAAAAAAAAAAAAAAAAAAAA/3////////////////////////////////wB///////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///3n//gAAAL3///////////////////////////////////////////////////////////////////////////////////////8D4AAAAAAAD//+AAAAAAAAAAAAAAAAAAAAH/4AAAAAAAAAAAAAAAAAAAAA/3////////////////////////////////wA///////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///Dj//gAAP//////////////////////////////////////////////////////////////////////////////////////////P4AAAAAAAD//8AAAAAAAAAAAAAAAAAAAAP/wAAAAAAAAAAAAAAAAAAAAA/j////////////////////////////////+E///////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///D///wAAf///////////////////////////////////////////////////////////////////////////////////////////4AAAAAAAD//+AAAAAAAAAAAAAAAAAAACf/AAAAAAAAAAAAAAAAAAAAAAfx/////////////////////////////////u////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///j////AA////////////////////////////////////////////////////////////////////////////////////////////8AAAAAAAD//+AAAAAAAB4AAAAAAAAAA3/4AAAAAAAAAAAAAAAAAAAAAAP4/////////////////////////////////0////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//n////gB////////////////////////////////////////////////////////////////////////////////////////////8AAAAAAAD//8AAAAAAAD8AAAAAAACBB/8AAAAAAAAAAAAAAAAAAAAAAAH4H////////////////////////////////wf///////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//n////wB////////////////////////////////////////////////////////////////////////////////////////////8AAAAAAAD//gAAAAAAAB+AAAAAAAPzh+QAAAAAAAAAAAAAAAAAAAAAAAD8H////////////////////////////////gP///////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///D////wD////////////////////////////////////////////////////////////////////////////////////////////8AAAAAAAB/+AAAAAAAAA/AAAAAz8//wwAAAAAAAAAAAAAAAAAAAAAAAAA+D////////////////////////////////Dv///////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///P////wH////////////////////////////////////////////////////////////////////////////////////////////8AAAAAAAA/+AAAAAAAAAHAA5GB////gAAAAAAAAAAAAAAAAAAAAAAAAAAeA////////////////////////////////3////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//+f////gP////////////////////////////////////////////////////////////////////////////////////////////8AAAAAAAA/8AAAAAAAAACAB/vB/+/8AAAAAAAAAAAAAAAAAAAAAAAAAAAEAf///////////////////////////////7////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//Af////A/////////////////////////////////////////////////////////////////////////////////////////////8AAAAAAAA/4AAAAAAAAAAAB5+A/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////////////////////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/8AP////B////////////////////////////////////////////////////////////////////////////////////////////v+AAAAAAAA/wAAAAAAAAAAAAh+ARAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfgAB/////////////////////////////////////////////////////////////////////////////////////////////////H+AAAAAAAG/gAAAAAAAAAAAAA+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////////////////////////////////z/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////////////////////////////////////////////////////////////////////////////////////////////H+AAAAAAAP+AAAAAAAAAAAAAAMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////////////////////////////////8H/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////////////////////////////////////////////////////////////////////////+P/AAAAAAAP4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////////////////////////////////4P/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////z////////////////////////////////////////////////////////////////////////////////////////////+P/AAAAAAAPwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////////////////////////wP/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/+UgH////////////////////////////////////////////////////////////////////////////////////////////+H/AAAAAAAfgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////////////////////////////////Af/nAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/8Hg/////////////////////////////////////////////////////////////////////////////////////////////+H/gAAAAAA/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////////////////4D/+AA//vgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA8A/x/////////////////////////////////////////////////////////////////////////////////////////////+H/wAAAAAB8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////////////////////////////3//+AB///wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////////////////////////////////////////////////////////////////////////////////+P/wAAAAAD4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////////////////////v/AB///4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////////////////////////////////////////////////////////////////////////////+P/wAAAAADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////////////////////////////////////x/AH///8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAff//////////////////////////////////////////////////////////////////////////////////////////////+P/4AAAAAHgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////////////////////////wOAP///+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////////////////////////////////////////////////////////////////////////8f48AAAAAPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////////////////////////////////////wAAf///+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////////////////////////////////////////////////////////////////////////8PwYAAAAAGAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////////////////gAAP///+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////////////////////////////////////////////////////////////////////////4HwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////////////////gBAf////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////////////////////////////////////////////////////////////////////////wHgAAAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////////////////gHgf////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////////////////////////////////////////////////////////////////////////gPgAAAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////////APgf////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////////////////////////////////////////////////////////////////////////////+APwAAAAAJAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////////////////////////+wPEMB//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////////////////////////////////////////////////////////////////////////////////8AP4AAAAAcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////////4GeAA//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////////////////////////////////////////////////////////////////////////////////4AP8AAAAA8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////////////////////////8/AA/3+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////////////////////////////////////////////////////////////////////////4Af+AAAAB4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////////////////////////gAaDcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////////////9////////8G/////////////////////////////////////////////////////////wAf+AAAAwgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////+A////////wAf////////////////////////////////////////////////////////gAP+AAAD4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////////////////5//4A///////+AA/////////////////////////////////////////////////////////AAPOAAAHwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////////////wH/79///////4AP/////////////////////////////////////////////////////////ABOEAAFngAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////gP//////////gA/////////////////////////////////////////////////////////+AD+AAAP/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////////////AP//////////AZ/////////////////////////////////////////////////////////4AD/AAAf0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////5///////////AH/////////8A//////////////////////////////////////////////////////////wAB/wAA/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////5//////////+AA//3//////4A//////////////////////////////////////////////////////////gAA/4Ad8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////w//////////8AA/wD//////4Af/////////////////////////////////////////////////////////AAAf+G/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////////////////////////H/8ABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////8H/////////wAAeAAf/////+Af////////////////////////////////////////////////////////+AAAf///gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////////////////////////////4H/gADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPAgAB//////8//+D/////////wAAAAAP//////AP////////////////////////////////////////////////////////4AAA////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////////////////////////////AH/AABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//9z//////wP//h/////////gAAAAAA//////AD////////////////////////////////////////////////////////4AAA////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////4AD+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////gH//wP////////gAAAAAAf////+AB////////////////////////////////////////////////////////wAAH////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////gAA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////8Az//wH////////AAAAAAAP////+AB////////////////////////////////////////////////////////gAAP///4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////w/4B///wB///////+AAAAAAAD/////AA///////////////////////////////////////////////////////+AAAf///gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////gDAH///4A///////+AAAAAAAB/////AAP//////////////////////////////////////////////////////4AAA///+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////wAAP///8AP//////8AAAAAAAAP////gAH////////////////////////////////////////////////////8fgAAB//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////wAAP4f//+A//////8AAB/4AAAH////wAD////////////////////////////////////////////////////wAAAAD//8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////wAAP4H///AP/////+AAP//AAAH////4AD////////////////////////////////////////////////////gAAAAD/h8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////wAAH4D///AH/////+AAf//gAAH////8AD///////////////////////////////////////////////////+AAAAAB/wYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////gAAHwA///AD///////j///8AA/////+AD7//////////////////////////////////////////////////8AAAAAA/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////8AAAL4AP//4D////////////////////ABx//////////////////////////////////////////////////8AAAAAAf4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////////////////////iwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////4AAAf8AH///D////////////////////AA///////////////////////////////////////////////////8AAAAAAf4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////+AAAAf8AB///n////////////////////4B///////////////////////////////////////////////////8AAAAAA/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////8AAAAf8AA///3////////////////////8B/////////////////////////////////////////////9/////4AAAAAA/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////4BuAAP8AAP///////////////////////8B/////////////////////////////////////////////4/////AAAAAAA/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////wD/AAP8AAB/n7///v////////////////4B/////////////////////////////////////////////x////+AAAAAAB/+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAAAAAAD//////gP/AAP8AAA/xx///P////////////////gA////////////////////////////////////////////+D////8AAAAAAA/+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAABwAAAAAAAAAAAAAH//////AfyAAP4AAAP4h///G////////////////AA////////////////////////////////////////////8H/9//gAAAAAAA/+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAABwAAAAAAAAAAAAAH//////DPwAAP4AAAP4A///x////////////////AA////////////////////////////////////////////4H/A//wAAAAAAA/+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAgC3AAAAAAAAAAAP//////nhgAAfwAAAP8AP//4////////////////AA////////////////////////////////////////////wP4AP/4AAAAAAB/+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/gAAAAAAAAAAP//////zgAAAPAAAAP4AP//8///////////////+AA///////////////////////////////////////////7APwAf/8AAAAAAB/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/AAAAAAAAAAAH//////hAAAAAAAPD/gAP//5///////////////8AAX//////////////////////////////////////////8gHgA//8AAAAAAz/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4CAAAAAAAAAAD//////AAAAAAAAf//AAf//9///////////////+AAH///////////////////////////////////////////wAAB//+AAAAAB7/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHgAAAAAAAAAD/////8AAAAAAAA///AAP//+///////////////+AAH///////////////////////////////////////////48AB///AAAAAB//gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHwAAAAAAAAAB/////8AAAAAAAA//+AAP///////////////////4AH///////////////////////////////////////////5/+A///gwAAA5//gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADgAAAAAAAAAB/////8AAAAAB+Af/wAAH///////////////////8AD///////////////////////////////////////////7//AN//h4AAB9//gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwAAAAAAAAAD/////4AAPg/v/wP/wAAA/8/5///////////////8AD/////////////////////////////////////////////+AA//wwAAB///gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB4AAAAAAAAAD////+AAD/////5D/wAAA/4/7////////////////AP/////////////////////////////////////////////+AB//4AAAB///gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwAAAAAAAAAB+P//+AH///////gfgAAAf5/////////////////////////////////////////////////////////////////8AB//4AAAB///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//8A///////5AHAAAAP8z////////////////////////////////////////////////////////////////oAB//4ADAD///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH+AAB///////gAMAAAAD4Hsff4/+H////////////////////////////////////////////////////////8AAA//4AHgH//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8AAf///////wAeAAAAASDA+PwP9D////////////////////////////////////////////////////////4AAA//4ADHv//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8BA////////4AeAAAAAH8B8AAHHn////////////////////////////////////////////////////////wAAA//4AP/////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//j////////4AMAAAAAP/7wAAH/n////////////////////////////////////////////////////////AAAA//4Af////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////4AAAAAAAP/9gAAP/D///////////////////////////////////////////////////////+AAAB//wB/////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////4AAAAAAAH/8AAAf+D///////////////////////////////////////////////////////8AAAD//wD/////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////8AAAAAAAAf4AAAP8D////////////////////////////////////////////////////////AAAD//4f/////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///////////4AAAAAAAAAAAAAHwH////////////////////////////////////////////////////////gAAD/34//////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////wAAAAAAAAAAAAABAH////////////////////////////////////////////////////////wAAB/h4////woAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////4AAAAAAAAAAAAAAAP////////////////////////////////////////////////////////wAAA4B7////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////4AAAAAAAAAAAAAAAP////////////////////////////////////////////////////////4AAA8A////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAT//////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////////8AAAAAAAAAAAAAAAf////////////////////////////////////////////////////////4AAB+B///++AAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA7//////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////+CAAAAAOAAAAAAAAf////////////////////////////////////////////////////////8AAB8D///8cABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAATn/////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOAAAAB///////////////4AAAB/wAAAAAAA/////////////////////////////////////////////////////////8AAA4D///YAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD3/////////////////////////AAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfAAAAD////////////////gAAP/4AAAAAAA/////////////////////////////////////////////////////////+AAAAH//+AAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABn////////////////////////+AAAAAAAAAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOAAAAH////////////////wAAf//AAAAAAA//////////////////////////////////////////////////////////AAAAHf/MAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////8AAAAAAAAAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////wAA///8AAAAAB//////////////////////////////////////////////////////////gAAACP+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////wAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////////////wAA///+AAAAAB//////////////////////////////////////////////////////////wAAAAP+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////////////4AA/////gA/wB//////////////////////////////////////////////////////////wAAAAf+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////gA/////4B/4///////////////////////////////////////////////////////////wAAAAP8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/7//////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////+A//////n/////////////////////////////////////////////////////////////wAAAAH4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf8f////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////////g////////////////////////////////////////////////////////////////////4AAAAD4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP8P////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////5////////////////////////////////////////////////////////////////////wAAAAB4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP8P////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////////////////////////////////////////////////////////////////////////////wAAAAD4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH8H/////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///////////////////////////////////////////////////////////////////////////////////////8AAAADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH+H/////////////////P///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////////////////////////////////////////////////////////////////////////////+AAAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/3////////////////AD///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////////////////////9f///////////////////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABgD/7///////////////+AB4f/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABAB///////////////////////////////////////wP///////////////////////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADwA//////////////A//+AAQP/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADgD///////////////////////////////////////gH///////////////////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADwAf////////////+AA/+AAAH/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABgAHgH///////////////////////////////////////wH///////////////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABgAP////////////4AACcAAAH/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADzwPAf///////////////////////////////////////4H///////////////////////////////////////////////wAAAAYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAn////////////gAAAAAAAH/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/8fB////////////////////////////////////////4D///////////////////////////////////////////////gAAAA8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABz/P//////////AAAAAAAAH/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/+ef////////////////////////////////////////8B///////////////////////////////////////////////gAAAB4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//H/////////8AAAAAAAAH/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADf+8/////////////////////////////////////////8A///////////////////////////////////////////////AAAADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//j/////////4AAAAAAAAH/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHveZ/////////////////////////////////////////+A//////////////////////////////////////////////+AAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/w/////////wAAAAAAAAH/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADAMB///////////////////////////////+P/////////Af/////////////////////////////////////////////8AAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/4/////////wAAAAAAAAD/8BwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////////////////////8H/////////gB/////////////////////////////////////////////4AAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/8f////////gAAAAAAAAD/+f4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////////////////////+H/////////4A/////////////////////////////////////////////wAAAAcAAAAAAAAGAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/+H////////wAAAAAAAAB/+/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///////////////////////////////+D/////////8AP/7//////////////////////////////////////////gAAAA8AAAAAAAAPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/+D////////wAAAAAAAAB/+feAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////////////////////+B/////////8gH////////////////////////////////////////////gAAAB8AAAAAAAAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/B////////wAAAAAAAAA/+MeAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////////////////////////+A//////////wAff//////////////////////////////////////////gAAAB4AAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/j////////wAAAAAAAAAf8A8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////////////////A//////////4AA///////////////////////////////////////////AAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/D////////wAAAAAAAAAP8AbAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////////////////g//////////4AB9//////////////////////////////////////////AAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/h////////wAAAAAAAAAH8DHgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////////////////////////w//////////4AD8//////////////////////////////////////////DgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/w////////gAAAAAAAAAH8H7wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////////////////////////wf/////////4AH8D////////////////////////////////////////+HwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/4H///////gAAAAAAAAAH4H94AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////////////////////////4H/////////4AP+ABf/3+f//////////////////////////////////8P4AMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/wD///////AAAAAAAAAAPwP58AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////////////////////////////4H/////////4k/+AABAAAf//////////////////////////////////wfwOeAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/+D///////AAAAAAAAAAfgHw+QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////////////////////8H/////////5///AAAAAAP//////////////////////////////////wfwfMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/B///////AAAAAAAAAAMAD4P4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////////////+D/////////////gAAAAAH//////////////////////////////////g/wfAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/Af//////AAAAAAAAAAAAD4W4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////////////////////////B/////////////9AAAAAH/////////////////////////////////+A/gOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/AH//////AAAAAAAAAAAAB4/QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////////////////////+Af/////////////gAAAAD/////////////////////////////////8B/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/gH//////AAAAAAAAAA6AAw/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////////////////////+AP/////////////wAAAAA/////////////////////////////////4B/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfgD//////AAAAAAAAAP/+AAfgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////////////////////+AH/////////////4AAAAAP////////////////////////////////wD/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPAB//////AAAAAAAAB///gAH+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////////////////////gH/////////////8AAAAAH///////////////////////////////+AD/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAGAA//////AAAAAAAAD////AD/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////////////////////wD/////////////+AAAAAD///////////////////////////////8AB/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////AAAAAAAAH////gAv8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////////////////////////4D//////////////AAAAAD///////////////////////////////gAB+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////AAAAAAAAf+///wAe9AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////////////////////////////4D//////////////AAAAAD//////////////////////////////4AAA+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/EAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADf/////AAAAAAAA//f//4AMbgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///////////////////////////////////8D//////////////AAAAAB//////////////////////////////gAAAcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB+OAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHv/////gAAAAH/g/PD//+AAXwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///////////////////////////////////+D/////////////+AAAAAA//////////////9//////////////4AAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgf4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHv/////wAAAB//wcfgP//wB7gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///////////////////////////////////+B/////////////8AAAAAAf////////////+h//////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADH/////gAAAD//wAPAA//8D4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////////////////////////////////D/////////////4AAAAAAP///////////jgA///////////3/5gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////wAAAH//wAAAAP//H4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////////////////////////////////B/////////////4AAAAAAH/f/////////gAAf/////////+B+AAAAAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////wAAAP//gAAAAH//zwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////////////////////////////////A/////////////4AAAAAAD+P/////////gAAf/////////8B+AAAAAAB4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////4AAAP//wAAAAB//4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////////////A/////////////4AAAAAAB8P/////////gAAP/////////wB+AAAAAAA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////8AAAP//gAAAAAf/88WAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////Af////////////wAAAAAAAAP/////////AAAH/////////gD/AAAAAAA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////8AAAP//AAAAOA//9//wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////AH///////////8gAAAAAAAAf////////+AAAD/////////AH/gAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////+AAAf/+AAAEfB//7//4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////////////AD///////////8AAAAAAAAAf////////8AAAD////////+AP/gAAAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////AAAf/+AAAPOAwAB//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////////////AB///////////8AAAAAAAAAf////////gAAAB////////8Af/gAAAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////gAB//+AAAPgAAAA///gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////////////AA///////////8AAAAAAAAAf///////+AAAAA////////8Af/AAAAAAHwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8AAAAAAAAAAAAAAAAAAAAAAAAAAAABAAAB//////4Af//+AAAHAAAAN///wABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////gA///////////8AAAAAAAAAf///////8AAAAA////////8Af+AAAAAAH4AAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAADgAAAf/////+H///8AAAAAD8Af///4/nwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////wAf//////////4AAAAAAAAAf///////4AAAAA////////8Af+AAAAAAf4AAAAAAAAAAAAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABAAAAH//////////8AAAAAH/g////9//zAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////////////////////////////4AP//////////AAAAAAAAAAP///////wAAAAAf///////+Af8AAAAAA/8AAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////8AAAAAH/w///////ngAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////////////////////////////8AP/////////+AAAAAAAAAAP///////gAAAAAD////////AP4AAAAAA/8AAAAAAAAAAAAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////4AAAAAD/wf//w///DyAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////////////////////////////+AH/////////+AAAAAAAAAAP///////AAAAAAD////////gHgAAAAAA/8AAAAAAAAAAAAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////4AAAAAB/gGB8AG//nnAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////////////////////AD/////////8AAAAAAAAAAH//////+AAAAAAD////////gAAAAAAAB/8AAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////8AAAAAA9AAA4AAAHH3AAAAAAAAAAAAAAAAAAAAAAAAQAAAAA/////////////////////////////////////gB/////////AAAAAAAAAAAH//////8AAAAAAD////////wAAAAAAAB/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////4AAAAAAAAAAAAAAAD/AAAAAAAAAAAAAAAAAAAAAAAA4AAAAB/////////////////////////////////////gD/////////AAAAAAAAAAAH//////4AAAAAAD////////4AAAAAAAA/+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////wAAAAAAAAAAAAAAAA/AAAAAAAAAAAAAAAAAAAAAAAB+EAAAB/////////////////////////////////////gH////////+AAAAAAAAAAAH//////AAAAAAAD////////8AAAAAAAA/+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////weAAAAAAAAAAAAAAAfAAAAAAAAAAAAAAAAAAAAAAAA/OAAAB/////////////////////////////////////wH////////8AAAAAAAAAAAH//////AAAAAAAH////////+AAAAAAAB/+AAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///////g/AAAAAAAAAAAAAAALgAAAAAAAAAAAAAAAAAAAAAAAfuAAAD/////////////////////////////////////wD///////+AAAAAAAAAAAAH//////AAAAAAAH/7///////gAAAAAAD/8AAAAAAAAAAAAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////t/4AAAAAAAAAAAAAAHwAAAAAAAAAAAAAAAAAAAAAAAHPAAAD/////////////////////////////////////0B///////AAAAAAAAAAAAAD/////+AAAAAAAH/z///////wAAAAAAH/8AAAAAAAAAAAAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////+AAAAAAAAAAAAAAHwAAAAAAAAAAAAAAAAAAAAAAAAPAAAD//////////////////////////////////////Af//////AAAAAAAAAAAAAD/////4AAAAAAAH/j///////wAAAAAAH/4AAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/wf//////gAAAAAAAAAAAAADgAAAAAAAAAAAAAAAAAAAAAAAAGAAAD//////////////////////////////////////gf//////AAAAAAAAAAAAAD/////gAAAAAAAD+B///////4AAAAAAD/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOAH//////4AAAAAAAAAAAAADwAAAAAAAAAAAAAAAAAAAAAAAA8AAAD//////////////////////////////////////g//////+AAAAAAAAAAAAAB/////AAAAAAAAB8B///////8AAAAAAD/gAAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////8AAAAAAAAAAAAADwAAAAAAAAAAAAAAAAAAAAAAAH+AAAP//////////////////////////////////////g//////8AAAAAAAAAAAAAA////4AAAAAAAAAAB///////+AAAAAAD/wAAAAAAAAAAAAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////8AAAAAAAAAAAAABwAAAAAAAAAAAAAAAAAAAAAAAP8AAAf//////////////////////////////////////wf/////wAAAAAAAAAAAAAA////4AAAAAAAAAAB///////+AAAAAAD/4AAAAAAAAAAAAAADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////8AAAAAAAAAAAAAB4AAAAAAAAAAAAAAAAAAAAAAAPwAAA///////////////////////////////////////4P////8AAAAAAAAAAAAAAAf///4AAAAAAAAAAB///////+AAAAAAD/4AAAAAAAAAAAAAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////8AAAAAAAAAAAAAA8AAAAAAAAAAAAAAAAAAAAAAAGAAAAf//////////////////////////////////////8P////4AAAAAAAAAAAAAAAf///8AAAAAAAAAAA////////AAAAAAB//AAAAAAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////8AAAAAAAAAAAAAAYAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////////////////////////+P///+AAAAAAAAAAAAAAAAP///8AAAAAAAAAAA////////AAAAAAA//+AAAAAAAAAAAAAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////8AAAAAAAAAAAAAA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////////////////////////////////f///8AAAAAAAAAAAAAAAAP///8AAAAAAAAAAA////////AAAAAAB///AAAAAAAAAAAAAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////4AAAAAAAAAAAAAA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////////////////////////////////////4AAAAAAAAAAAAAAAAP///8AAAAAAABAAA////////AAAAAAD///gAAAAAAAAAAAAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////4AAAAAAAAAAAAAAwwAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////////////////////////////+AAAAAAAAAAAAAAAAAH///8AAAAAAADgAAf///////AAAAAAB///AAAAAAAAAAAAAeAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////4AAAAAAAAAAAAAB54AAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////////////////////////////4AAAAAAAAAAAAAAAAAH///8AAAAAAAHgAAf///////AAAAAAA//+AAAAAAAAAAAAAcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///4AAAAAAAAAAAAABw4AAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////////////////////////////4AAAAHgAAAAAAAAAAAAH///8AAAAAAAHgAAf+//////gAAAAAAf//AAAAAAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//4AAAAAAAwSAAAABwQAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////////////////////////////wAAAAPwAAAAAAAAAAAAH///8AAAAAAAHgAAf///////gAAAAAAf//4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//4AAAAAAD4/oAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////////////////////////////AAAAAf4AAAAAAAAAAAAD///8AAAAAAAHgAA/+//////gAAAAADv//8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//wAAAAAAH8/8AAAHgAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////////////////wAAACAPwAAAAAAAAAAAAB///4AAAAAAAHgAA/+V/////AAAAAAH///+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//wAAAAAAP9/8AAAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////////////////gAAAHgHgAAAAAAAAAAAAB///wAAAAAAAPgAAf+B/////AAAAAAH3//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//wAAAAAAf9/oAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////////AAAA/wAAAAAAAAAAAAAAA///wAAAAAAAPAAA/8A/////AAAAAADg//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/wAAAAAP/7/wAAYAMAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////////////////////////////////AAF//wAAAAAAAAAAAAAIAf//wAAAAAAAPAAAf8A/////AAAAAAHg//+AAAAAAAAAAAAAAAAAAAAAAAAAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/wAAAAB////4AZ8AeAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////////gAf//gAAAAAAAAAAAAAcAf//wAAAAAAAHAAAf4Af///+AAAAAAPA///AAAAAAAAAAAAAAAAAAAAAAAAAAB4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/4AAAAD////8C///8AAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////////w////gAAAAAAAAAAAAAIAf//wAAAAAAAOAAA/4AP///8AAAAAAeA///AAAAAAAAAAAAAAAAAAAAAAAAAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/4AAAAH//////Z//4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAz////////////////////////////////////////////wAAAAAAAAAAAAAAAP//wAAAAAAAeAAAfwAH///wAAAAAAfA//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/4AAAAP//////x//4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////////////4AAAAAAAAAAAAAAAP//wAAAAAAAeAAAPwAD///AAAAAAA/g///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/8AAAAf/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////////////////////////////////////wAAAAAAAAAAAAAAAP//wAAAAAAAMAAAfwAB//8AAAAAAB/Af//gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/+AAAAP/////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////////////////////////////////AAAAAAAAAAAAAAAAH//8AAAAAAAAAAA/0AA//wAAAAAAB8AP//wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//gD8Af//v//////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////////////////////////////////////AAAAAAAAAAAAAAAAH//+AAAAAAAAAAAf+AAT/gAAAAAAD4AP//wAAAAAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//wP/A//////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////////////////////////////////////AAAAAAAAAAAAAAAAH//+AAAAAAACAAAP+AAH/gAAAAAAHgAP/vgAAAAAADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA3/4//h//////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////////////////////////////////AAAAAAAAAAAAAAAAD///AAAAAAAHAAAf+AAH/AAAAAAAfgAH9/wAAAAAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////7//////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////////////////////////////AAAAAAAAAAAAAAAAD///gAAAAAACAAAf+AAH5gAAAAAA/AAD5/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////////////////////////////+AAAAAAAAAAAAAAAAD/w/wAAAAAAAAAAf+AAHzwAAAAAB+AAB7/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////////////////////////////8AAAAAAAAAAAAAAEAB/x/wAAAAAABwAAf/AAHhgAAAAAB8AAD//wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////////////////////////////4AAAAAAAAAAAAAAOAA/h/4AAAAAAD4AAf/AADAAAAAAABwAAP//4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/8/////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////////////////////////////wAAAAAAAAAAAAAAEAAeB/4AAAAAAB4AAf/AAAAAAAAAADgAAf//4AAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAGP+H/////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////////////////////////////wAAAAAAAAAAAAAAAAAEB/8AAAAAAA4AAf/gAAAAAAAAADgAA///4AAAAHAAAAAAAAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf+H/////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////////////////////////////wAAAAAAAAAAAAAAAAAAB/8AAAAAAAcAAP/gAAAAAAAAABgAA///4AAAAPAAAAAAAAAAD4AAAAAAAAAAIBAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf8D/////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////////////////////////////gAAAAAAAAAAAAAAAAAAB/8AAAAAAA8AAB/sAAAAAAAAADwAA///4AAAAOAAAAAAAAAADwAAAIAAAAAAcD4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAN4B/////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////////////////////////////////////AAAAAAAAAAAAAAAAAAAB/+AAAAAAAeAAA/+AAAAAAAAAHwAA/P/4AAAAEAAAAAAAAAABgAAAcAAAAAAID8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////////////////////////AAAAAAAAAAAAAAAAAAAB/8AAAAAAAeAAAf+AAAAAAAAAH4AB8P/wAAAAAAAAAAAAAAAAAAAAcAAAAAAAB4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///////////////////////////////////////+AAAAAAAAAAAAAAAAAAAA/8AAAAAAAMAAA//gAAAAAAAAP8AB8P/wAAAAAAAAAAAAAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////////////////////////////////+AAAAAAAAAAAAAAAAAAAA/4AAAAAAAAIAAf/wAAAAAAAAf8AH4H/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////+B/////////////////////////////+AAAAAAAAAAAAAAAAAAAAfwAAAAAAAAcAAP/4AAAAAAAA//APgD/gAAAAAAAAAAAAAAAAAAAAAAAAAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAA///////+AA/////////////////////////////8AAAAAAAAAAAAAAAAAAAAPAAAAAAAAAeAAH/8AAAAAAAB//4HAB+AAAAAAAAAAAAAAAAAAAAAAAAAAAADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////8AAf////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/AH/+AAAAAAAD///iAAcAAAAAAAAAAAAAAAAAAAAAAAAEAAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////+AAAf////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/wH//AAAAAAAP///wAAIAAAAAAAAAAAAAAAAAAAAAAAAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAH/////4AAAP////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/4D//AAAAAAAf///gAAAAAAAAAAAAAAAAAAAAAAAAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAD//wD/AAAAP////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/4D//gAAAAAB///7AAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAA/8AAMAAAAH////////////////////////////gAAAAAAAAAAAAAAABAAAAAAAAAAAAAAH/8D//gAAgAAD///gAAAAcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAGAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAPwAAAAAAAD////////////////////////////AAAAAAAAAAAAAAAADgAAAAAAAAAAAAAD/+D//gABwAAD///gAAAAeAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAADAAAAAAAAB4D/////////////////////////+AAAAAAAAAAAAAAAABAAAAAAAAAAAAAAB//B//gAD4AAH///AAAAEcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//h//AAD4AAP//8AAAAOcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAGAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPf////////////////////////8AAAAAAAAAAAAAAAABAAAAAAAAAAAAAAAf/4//gCBwAAf//8AAAAPIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPP////////////////////////4AAAAAAAAAAAAAAAADgAAAAAAAAAAAAADH/8f/gPAMAH///8AAAAGAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAGP////////////////////////wAAAAAAAAAAAAAAAABAAAAAAAAAAAAAAHn/+f/ofAeA////8AAAAMAAAcAAAAAAAAAAAAAAAAAAAAAAAAAAB4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHz//f/8eAcB////8AAAAeAOAIAAAAAAAAAAAAAAAAAAAAAAAAAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////4IAIB////+AAAAMAfAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////4AABh////+AAAAAA+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAAAAAAAAAAAAAAAAAADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABAf///////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA3////4AAD9////+AAAAYB+AAAAAAAAAAAAAAAAAAAAAAAAAAAAA4AAAAAAAAAAAAAAAAAADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADgf///////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHP///8AAH//////AAAB8D+AAAAAAAAAAAAAAAAAAAAAAAAAAAAA4AAAAAAAAAAAAAAAAAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHg////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPn///8AAP//////gPAD8D/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADA///////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHz///+AAP//////w//j4D/AAAAAAAAAAAAAAAAAAAAAAAAAAAAA8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH7////AAP//////5///4D/AAAAAAAAAAAAAAAAAAAAAAAAAAAAA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIA///////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD7///+AAP//////z///wH+AAAAAAAAAAAAAAAAAAAAAAAAAAAAA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgAAAAAAP///////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAcB///////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABz///sAAP//////j///gD/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABwAAAAAAP////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA8B///////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAt///+AAP/////4H///AD/jwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8AAAAAAf////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA8B//////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAe////AAH/////4HgA8AD/34YAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH+AAAAAA/////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAYD//////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOf///gAP/////4HgxgAH4/98AAAAAAAAAAAAAAAAAAAAAAQAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/YAAAAA//////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAeP///AAP/////4Hh/wAP4T//wcAAAAAAAAAAAAAAAAAAAA4BAAA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/8AAAAB///////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPH//8AAH/////4Hz/4AH8D//7/AAAAAAAAAAAAAAAAAAAAQDgAA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD+4AAAAD///////////////////////9AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHj//+AAH/////wP//4AD+D////gAAAAAAAGAAAAAAAAAAAADgAAYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB+QAAAAB////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPj//+cAP/////gf//4AD8B////HAAAAAAAPAAAAAAAAAAAABAAAcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEAAAAAB////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHz//++Af/////Af//7/j8P//9//4AAAAAAPAAAAAAAAAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH5////Ac////+Af/7//z8f//8//+AAAAHwGAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD9////AI////+Af/z//h4fj/+f//4AAAP8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA9////jA////+Af/xJ/gAPB/+H///AAAP+B4AAAAAAAAAAAAAAAAAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////////////nwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAe////3gf///+A//4ADgP4B//H///4AAHsD+QAAAAAAAAAAAAAAAAAAAAAAAdAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPf////wf///8B//4AB4//D//P///+AAAAB/+AAAAAAAAAAAAAAAAAAAAAAALgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHv////wf///8B//8AD///j///////4AAAA//AAAAAAAAAAAAAAAAAAAAAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHv////wP///8B//+AD///x///////+AAAAD/AAAAAAAAAAAAAAAAAAAAAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADH//+HgAf//+B//8AD///wf///////wAAAB+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//+AAAPD/+A///gB/+3wf///////4AAAAfYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//+AAAAAf8AP3/wAecDgf///////8AAAB/8AAAAAAAAAAAAAAAAAAAAAAiAAAAAAAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////////8AAAAAAAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//8AAAAAeQAPz/wAAAAAPv//////+QAAD/4AAAAAAAAAAAAAAAAAAAAEB3AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////4AAAAAAAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/+AAAAAIAAP7/wAAAAADD///////4AAB/gAAAAAAAAAAAAAAAAAAAAOAiAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////4AAAAAAAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/+AAAAAAAAP7/wAAAAAAA///////4ABj/hgAAAAAAAAAAAAAAAAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////8AAAAAAAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABj/+AAAAAAAAPx/4AAAAAGAD//////xgD3/DwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADw/+AAAAAAAAfx/8AAAAAPGA//////////8DwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB4/8AAABgAAAP4/4AAAAAePAD/////////4B4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwf/8AADwAAAH4fEAAAAAefAD/////////wB8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//gABgAAAC4COAAAAAefAB/////////AB+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//wDAAAAAA4AEAAAAAM/gA//////8/+AA/QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///H8BDAAA4AAAAAAAA/AA//////8P4AAf4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////3gAAYAAAAGADA/AAf/////8AAAAf+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////4AAAAAAAAAAAAAAAAAAAAAwAAAAAAAAAAAAAAAAAAAAA///////gAAcAAAAPAHgeAA//////4AAAAPfAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////4AAAAAAAAAAAAAAAAAAAAB4AAAAAAAAAAAAAAAAAAAAAD/////7AAAIAAATPAPgIAB//////wAAAACfmAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////8AAAAAAAAAAAAAAAAAAAAA4AAAAAAAAAAAAAAAAAAAAAD/////wAAAAAAD/mYfAAAD//////4AAAAA/vAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////////////////AAAAAAAAAAAAAYAAAAAAAAAAAAAAAAAP/////////////////+AAAAAAAAAAAAAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAB/////6AMAADAH/g8+AAAD//////+AAAAA/PwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////////////////AAAAAAAAAAAAA8AAAAAAAAAAAAAAAAAH/////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////u/48H///w88AAAH///////AAAAA/n5gAAAAAAAAAAAAAAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////////////+AAAAAAAAAAAAAYAAAAAAAAAAAAAAAAAD/////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////4Z8AAAH////B//AGAAA/7/wAAAAAAAAAAAIAAAADgAAAAAAAAAAAAAAAAAAAANAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////wA4AAAH///+Af/APAAAX8/4AAAAAAAAAAAcAAAABAAAAAAAAAAAAAAAAAAAAAfgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABj////////+AAAAAADsP/+AP/4OHAAH9/4AAAAAAAAAAAIAAAAACAAAAAAAAAAAAAAAAAAAAfgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA3////+H/8AAAAAAAAH/+AH/90PgAD7/8AAAAAAAAAAAAAAAAAHAAAAAAAAAAAAAAAAAAAAfAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP4fmgP/wAAAAAAAAD/8AD//8HgAAB/+AAAAAAAAAAAAAAAAACAAAAAAAAAAAAAAAAAAAAe4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/4Af/AAAAAAAAAA/gAD//+DAAAA/+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAN8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/8Af4AAAAAAAAAAGAAB//+AAAAAf+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf8A/wAAAAAAAAAAPAAA///AAAAAP+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAYAAAAAAAAD8x/gAAAAAAAAAAHAAAf//AAAAAB/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAeAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA8AAAAAAAAA57/AAAAAAAAAAAHAAAH/+AAAAAAPwAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAYAAAAAAAAAA34AAAAAQAAgAAHgAAAD+AAAAAAHwAfAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////gCAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHwAAADf4ABwAAHwAAAA0AmAAAADgAOAAAAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////gHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADAAAAH/8ADwAAHwAAAAAB/AAAEAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////gHgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//wHgAAHwAAAAAB/AAAPAAABwAAAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////gHkAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP9/+fAAAP4AAAAAA+AAAHgAAB4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////gDuAAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMAAAAAAAAAAAAAAAAAAAAAH////wAAf8AAAAAAQAAADAAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////gB+AAPgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAeAAAAAAAAAAAAAAAAAQAAAB////4AAf8AAAAAAAAAAAAAAAAAAAAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////gAtgAfgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMAAAAAAAAAAAAAAAAA4AAAD////wAAf8AAAAAAAAAAAAAAAAAAAAADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////gADwAPwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAAAD////gAAf+AAAAAAAAAAAAAAAAAAAAABgAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////gADwAv4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////gAA/+AAAAAAAAAAAAAAAAAAAAAAAAAAcADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////////gABgB/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////gAAf+AAAAAAAAAAAAAAAAAAAAAAAAAAIAH4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////gAAAD/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMAf////wAA/+AAAAAAAAAAAAAAAEAAAAAAAAAAAAH8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////gAAAD/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/Af////4AA/+AAAAAAAAAAAAAAAOAAAAAAAAAwAAD+wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////gAAAD/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/g/////wAA//wAAAAAAAAAAAAAAOAAAAAAAAB4AAAd4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////wAAAH/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/w/////4AA//4AAAAAAAAAAAAAAOAAAAAAAAAwAAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////wAAAP/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//+/////wAA//+AAAAAAAAAAAAABkAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////wAAAf/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////4AAA///AAAAAAAAAAAAADxgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////wAAAf/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////8AAAf//AAAAAAAAAAAAAB7wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////////wAAB//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////wAA///AAAAAAAAAAAAAB/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////////gAAP//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////4AA///AAAAAAAAAAAAAB/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB4BAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////gAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAAAH///////////////////AAB///+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////4AA///AAAAAAAAAAAAAB/wAAAAAAAgAAAAAAAAAAAAAAAAAAAAAD4DgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////////////gAAAAAAAAAAAAAAAAAAAABwAAAAAAAAAAH//////////////////+AAH///8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////+AA///gAAAAAAAAAAAAA/wAAAAAAHwAAAAAAAAAAAAAAAAABAAADwxAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///////////////////////gAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAAAH//////////////////+AAP///4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////Dh///gAAAAAAAAAAAAAfwAAAAAB/wAAAAAAAAAAAAAAAAADgAABB4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////8AAP///wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////x///gAAAAAAAAAAAAAPwAAAAAD/wAAAAAAAAAAAAAAAAADwAAAA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////4AAP///4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///////////h///wAAAAAAAAAAAAAH4AAAAAj/0AAAAAAAAAAAAAAAAADgAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////gAAf///4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////j///4AAAAAAAAAAAAABwAAAABz/uAAAAAAAAAAAAAAAAABB4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////AAAf///wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////3///4AAAAAAAAAAAAAAwAAAAB//EAAAAAAAAAAAAAAAAAAD8AAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////8AAA////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////4AAAAAAAAAAAAAB4AAAAA/+EgAAAAAAAAAAAAAAAAAB8AAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////gAAA////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////8AAAAAAAAAAAAAB4AAAAB/8PwAAAAAAAAAAAAAAAAAAYAAAADwAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////+AAAA////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////4AAAAAAAAAAAAAAwAAAAB/8HgABAAAAAAAAAAAAAAAAAAAAADwAPgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////+AAAA////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////////8AAAAAAAAAAAAAAEAAAAA/oCAADgAAAAAAAAAAAAAAAAAAAABwAHwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////8AAAA////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////8AAAAAAAAAAAAAAOAAAAAfAhAADgAGAAAAAAAAAAAAAAAAAAAgABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////4AAAAf///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////8AAAAAAAAEAAAAAPAAAAAHAzgABAAPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////////wAAAAf//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////////////AAAAAAAAOAAAAAHAAAAAPgjgAAAAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////AAAAAP//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////wAAAAAAAOAAAAAHAAAAAPABAAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////+AAAAAP//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////8AAAAAAAEAAAAAHgAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////4AAAAAP//8AAAAAYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///////////////////QAAAAAAAAAAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////wAAAAAP//8AAAAA8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////4AAAAAAAAAcAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////wAAAAAf//8AAAAB8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////////////////4AAAAAAAAA+BgB4AAAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////wAAAAA///4AAABB8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADH/////////////////////4AAAAAAAAAfj4AwAAAAAAHAAgAAAAAAAAAAAAAAAAAAAAAAAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////4AAAAA///4AAADg4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////////4AAAAAAAAAfz8AAAAAAAACABwAAAAAAAAAIAAAAAAAAAAAAAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////4AAAAB///4AAAHwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////////4AAAAAAAAAP5/AAAAAAAAAAB4AAAAAAAAAcAAAAAAAAAAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////4AAAAD///wAAAHwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////////8AAAAAAAAAH8fgAAAAAAAAAA4AAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////8AAAAD///wAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABP//////////////////////+AAAAAAAAAD/PwAAAYAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////8AAAAH///wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////AAAAAAAAAA/zgAAA8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////+AAAAH///wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////wAAAAAAAAAf5AAAAYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////+AAAAH///gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////4AAAAAAAAAH8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////+AAAAH///gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////8AAAAAAAAAD+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////+AAAAH///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////8AAAAAAAAAAuAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////+AAAAD///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////8AAAAAAAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////+AAAAD///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////+AAAAB//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////+AAAAB//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////+AAAAB//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////GAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////+AAAAB//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////8AAAAB//8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////8gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////4AAAAA//8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////wAAAAA//4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////4AAAAAAf/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAX//////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////wAAAAAAP/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////////AAAAAAAB4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABgAAAAAAAAAAAAAAAAAAAAAAAAH//////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADwAAAAAAAAAAAAAAAAAAAAAAAAH//////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADwAAAAAAAAAAAAAAAAAAAAAAAAP//////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABgAAAAAAAAAAAAAAAAAAAAAAAAP//////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////////////4AAAAAAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////////////4AAAAAAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////////////wAAAAAAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////wD/////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////8AA/////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////gAAD////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////8AAAAA////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////wAAAAAf///////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAYAAAB/////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////gAAAAAf///////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA8AAAB////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////+AAAAAAP///////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA8AAAB////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////8AAAAAAD///////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAYAAAD////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////4AAAAAAB///////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///wPwAAAAAAB/v////////+AAAAAAAAAAAAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//4AYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//8AAAAAAAAAD+P////////+AAAAAAAAAAAAAB8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//4AAAAAAAAAB+f////////8AAAAAAAAAAAAAB/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////+/+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/AAAAAAAAAAA+/////////8AAAAAAAAAAAAAA/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////MwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH+AAAAAAAAAAAM/////////8AAAAAAAAAAAAAA/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////4AAAAAAAAAAAAAAf4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////wAAAAAAAAAAAAAAP5AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/3///////wAAAAAAAAAAAAAAH7gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/B///////gAAAAAAAAAAAAAAD/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////gAAAAAAAAAAAAAAD/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////gAAAAAAAAAAAAAAB/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////gAAAAAAAAAAAAAAA/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////gAAAAAAAAAAAAAAAf4GAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////gAAAAAAAAAAAAAAAf8PAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////AAAAAAAAAAAAAAAAf//gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////8AAAAAAAAAAAAAAAAf//gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////8AAAAAAAAAAAAAAAAAf//AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////wAAAAAAAAAAAAAAAAA///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAT/P/AAAAAAAAAAAAAAAAAB///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAeB+AAAAAAAAAAAAAAAAAD//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABAeAAAAAAAAAAAAAAAAAH//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADgEMAAAAAAAAAAAAAAAAH//sAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHgAeAAAAAAAAAAAAAAAAD//gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHwAfAAAAAAAAAAAAAAAAA//gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADoAPgAAAAAAAAAAAAAABwH/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfAfgAAAAAAAAAAAAAAD7H+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfz/AAAAAAAAAAAAAAAH/v+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//AAAAAAAAAAAAAAAH//8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////9/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//AAAAAAAAAAAAAAAP//4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////+OAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//AAAAAAAAAAAAAAAf//wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////+YAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//AAAAAAAAAAAAAAA//3gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//AAAAAAAAAAAAAAB//gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//AAAAAAAAAAAAAAB//gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//AAAAAAAAAAAAAAD//AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//AAAAAAAAAAAAAAP/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/+AAAAAAAAAAAAAAf/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/+AAAAAAAAAAAAAB//4AAAAAA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB+/////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/8AAAAAAAAAAAAAH//wAAAAAB8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfgAAAAAAAAAAAAA///4AAAAAB8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAv/////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///4AAAAAA+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//+QAAAAAAMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABwAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAE//////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH7AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADeAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAGAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////AAAAAHXAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAGAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////gAAAAP/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////gAAAA//8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////gAAAB//8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////wAAAA//4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////4AAAAf/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAGAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////wAAAAO8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAGAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////gAAAAAAAAAAAAAAAAAAH4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////4AAAAAAAAAAAAAAAAAAP+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////AAAAAAAAAAAAAAAAAAH/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAL////74AAAAAAAAAAAAAAAAD/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////8AAAAAAAAAAAAAAAAAPwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////4AAAAAAAAAAAAAAAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///6AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABf/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAeAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB4AAAAAfAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/AAAAAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA7AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAJ//gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA9/4AcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB8+AP/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA4MD//4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAcf//wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAe///+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAO////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///+fAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABg//wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4fAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADz//AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAAOAAAAH8PgAAAAB4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//gAAAAAAAAAAAAAAAAAAAAAAAfAAcAH//4AAAB//AAAAAAAAAAAADAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf///+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///4AAAAAAAAAAAAAAAAAAAAAAAOAA+CH///AAAH//gAAAAAACAAH//7+YAAAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACf///8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////gAAAAAAAAAAAAAAAAAGAAAH/h5//P////+AP//+AAAAAGP4AP/////+AAAAAAAAAAAAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfv///wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA4f////wAAAAAAAAAAAAAAAAAPuH/////////////8////gAAAP//8Af///////+AAAAAAAAAAAAB+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///96AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/f////8AAAAAAAAAAAAAAAAAf////////////////////3mPh///////////////wAAAAAAAAAAA/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///8wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB4///////gAAAAAAAAAAAAAAAB////////////////////////////////////////4AAAAAAAAAAAHCAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///YAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8/////////5/AAAAAAAAAAAB/////////////////////////////////////////5wAAAAAAAAAACHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB///////////////x4AAAAAAA///////////////////////////////////////////4AAAAAAAAAAAHgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////8AAAAAD/////////////////////////////////////////////AAAAAAAAAAADAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABz//AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/////////////////4AAAAAP/////////////////////////////////////////////gAEAMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////8AAAAAf///////////////////////////////////////////////+AeAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMAAAAAAAAAAAAfgB///gYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD+AAAH///////////////////+AAAAA///////////////////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAeAAAAAAAAAAAD/wD///A8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/AAAP///////////////////8AAAAD////////////////////////////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMAAAAAAAAAAAH/4J///8YAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/gAAf///////////////////8AAAA//////////////////////////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/8////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/4AAf///////////////////8AAAH///////////////////////////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADw////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfgAAAAAAAAAD///4////////////////////4AD4v///////////////////////////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP4f///////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHAAAAAAAcA/wAAAAAOAAAP////////////////////////wAP//////////////////////////////////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf4P///////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADgAPgHAAgwA///geAMAAfAB//////////////////////////gCf//////////////////////////////////////////////////////////w4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP8B///////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHAHwAPnvgf/+B/////A/Dw/Af//////////////////////////wHf//////////////////////////////////////////////////////////5+HgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//B///////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/wP8AHP///////////B//4ff///////////////////////////wH///////////////////////////////////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//u///////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA8H/4P+AD/////////////////////////////////////////////wH////////////////////////////////////////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADh/H///8wf/////////////////////////////////////////////gH////////////////////////////////////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB//////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH//n////7/////////////////////////////////////////////+AP/////////////////////////////////////////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABx4MAAAAAAAAAAAAAn/////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////////////////////////////////////////////////////8B//////////////////////////////////////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////wAAAAAAAAAAAAP////9////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAb/////////////////////////////////////////////////////yP///////////////////////////////////////////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH////4AAAAAAAAAAAAH////4////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA8/////////////////////////////////////////////////////nf///////////////////////////////////////////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////AD4AAAAAAAAAD////4////8AAAAAAAAAAAAAAAAAAAAAAAAAAAABgA//////////////////////////////////////////////////////P///////////////////////////////////////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////wH8/gAAAAAAAEM///z////8AAAAAAAAAAAAAAAAAAAAAAAAAAAADwP//////////////////////////////////////////////////////f///////////////////////////////////////////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADB//////4D//wAAAAfAAf7f/+//////AAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////////////////////////////////////////////+////////////////////////////////////////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/AAAAAAAAAAAAAHx////////////AAD/wA//n////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/4AAAAAAAAAAAAD4////////////+AH//+//f////////gAAAAAAAAAAAAAAAAAAAAAAAAAQAB////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//j/88AQAAAAAABwf////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAB4AD///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////n4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/////+H4PwAAAAAAf///////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAf4AD//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////+BwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABwAO/////+P8f4P4AAAAf///////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAA/4AP/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////8AAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP8Afj////////4f8AAAAP///////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAf4Af/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///+D//////////8/8AAAAAf//////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAD4B//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAR/////////////////8AABJ4P//////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAwH//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////////////////////5/////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////8wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPAfz////////////////////////////////////////////////////YAAAAAAAAAAAAAAAAAAAAAAAAAAA//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfv//////////////////////////////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABnf//////////////////////////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAf/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////////////////////////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAH///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAB////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////////////////////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAAAAH////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAGDEAAf/////////////////////////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAD/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////8AAAAAAAAAAAAAAAAAAAAAAAAAP//8B//////////////////////////////////////////////////wH//wAAAAAAAAAAAAAAAAAAAAAAAH///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////ABwAAAAAAAAAAAAAAAAAAAAAAf////////////////////////////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAAAAA////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////gD/+AAAAAAAAAAAAAAAAAAAAAf////////////////////////////////////////////////////////8AAAAAAAAAAAAAAAA/wAAAAAAH////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////wH//AAAAAAAAAAAAAAAAAAAAA/////////////////////////////////////////////////////////4AAAAAAAAAAAAAAA///4AAAAAf////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////8X/+AAAAAAAAAAAAAAAAAAAAA/////////////////////////////////////////////////////////wAAB4AAAAAAAAAAB///+AAAAA////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAf////////////////////////////////////////////////////////gAAf8AAAAAAAAAAP////AAAAD////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////AAAAAAAAAAAAAAAAAAD+AAA/////////////////////////////////////////////////////4HgAAf/8AAAAAAAAAAf////AAAAH///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////+AAAAAAAAAAAAAAAAAAP/4AAP////////////////////////////////////////////////////4AAAP//4AAAAAAAAAA/////gAAAH///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////4AAAAAAAAAAAAAAAAAAf//wAH/////////////////////////////////////////////////+///AAA///wAAAAAAAAAA/////wAAAH/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////4DwAAAAAAAAAAAAAAAAAAf//+AAP////////////////////////////////////////////////////wAB////AAAAAAAAAB/////4AAAP////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////IAAAAAAAAAAAAAAAAAAAAAP///AA4An//////////////////////////////////////////////////4AB/+//wAAfgAAAAD/////4AAAH/x/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAH///gB/wA//////////////////////////////////////////////////4AA/4f/4AD/wAAAZv/////4AAAAAA/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAA//AA/4AH/////////////////////////////////////////////////4AAfwA/4Af/4AAA///////4AAAAAAf////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAHwAP/////////////////////////////////////////////////8AAEAAf////8AAD///////wAAAAA//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////////////////////////////////////////cH/gAP////4AAH///////AAAAA///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH///////////////////////////////////////////////////////4D////wAAH/////AAAAP/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAH8AAAf//////////////////////////////////////////////////////////8AAx//gAAD///gAAAAf//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////wAAAAAAAAAAAAAAAAAAAAAAP//AA////////////////////////////////////////////////////////////////+AAAAAAAAAAAB///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////+AAAAAAAAAAAAAAAAAAAAAAP//hAf//////////////////////////////////////////////////////////////8AAAAAAAAAAAAH////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////4AAAAAAAAAAAAAAAAAAAAAH//D+H//////////////////////////////////////////////////////////////8AAAAAAP///wA//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////AAAAAAAAAAAAAAAAAAAAAAAAB/AH//////////////////////////////////////////////////////////////8AAAH/////4f//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////iAAAAAAAAAAAAAAAAAAAAAAAA+AD//////////////////////////////////////////////////////////////+AAH///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////AAAAAAAAAAAAACAYAAAAD4AAAAP//////////////////////////////////////////////////////////////8AD/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////wAAAAAAAAAAAH///AAAH/gAB////////////////////////////////////////////////////////////////gA///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////wAAAAAAAAAAD//////H/wAD////////////////////////////////////////////////////////////////wD///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////4AAAAAAAAAAB//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////wAAAAAAAAAAH//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////8AAAAAAAAAA///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////wA/wAAAAAD/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////4AAAH//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////8H//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////"  # 720x360 бит (0.5°): 1 = суша (с запасом по берегам)
import base64 as _sifa_b64
_sifa_land = _sifa_b64.b64decode(SIFA_LAND_MASK_B64)

def sifa_is_land(lat: float, lon: float) -> bool:
    r = min(719, max(0, int((90.0 - lat) * 4)))      # 0.25° на клетку
    c = min(1439, max(0, int((lon + 180.0) * 4)))
    return bool((_sifa_land[r * 180 + (c >> 3)] >> (7 - (c & 7))) & 1)

def sifa_area_ok(area, lat, lon):
    """Точка внутри области игры? maxLon > 180 — область пересекает меридиан 180°."""
    if not (area[0] <= lat <= area[2]):
        return False
    if area[3] <= 180.0:
        return area[1] <= lon <= area[3]
    w = (area[3] - area[1]) % 360.0
    u = (lon - area[1]) % 360.0
    return u <= w

def sifa_random_water(area):
    import random as _rnd
    for _ in range(800):
        if area:
            lat = _rnd.uniform(area[0], area[2])
            if area[3] > 180.0:
                w = (area[3] - area[1]) % 360.0
                lon = ((area[1] + _rnd.uniform(0.0, w) + 540.0) % 360.0) - 180.0
            else:
                lon = _rnd.uniform(area[1], area[3])
        else:
            lat = _rnd.uniform(-58.0, 72.0)
            lon = _rnd.uniform(-180.0, 180.0)
        if not sifa_is_land(lat, lon):
            return lat, lon
    return 25.0, -40.0   # Средина Атлантики — гарантированная вода


# ---------- Следопыт: человечек по суше России, Пища, вокзалы (клад — фаза 2) ----------
WALKER_SPEED_KM_PER_MIN = 30.0   # «прогулочный» темп игры, не реализм
WALKER_ENERGY_MAX = 800.0        # запас хода, км
WALKER_FOOD_ENERGY = 250.0       # 1 единица Пищи -> +250 км энергии
WALKER_START_FOOD = 5            # стартовый запас Пищи у нового следопыта
FOOD_COOK_SEC = 3600             # готовка: 1 единица раз в час (плавающий кулдаун)
FOOD_DAILY_MAX = 24              # не больше 24 единиц в сутки (сброс в 00:00 МСК)
FOOD_MAX_STOCK = 10              # вместимость «сумки» с едой
WALKER_FILE = "walker.json"
# территория: Россия, lat 41..82; lon 19..180 и -180..-169 (Чукотка через антимеридиан)
# формат области как у Сифы: [lat_min, lon_min, lat_max, lon_max], lon_max > 180 = переход
WALKER_AREA = (41.0, 19.0, 82.0, 191.0)
WALKER_STATIONS = [
    {"key": "bry", "name": "Брянск",      "lat": 53.2521,  "lon": 34.3717},
    {"key": "nsk", "name": "Новосибирск", "lat": 55.0302,  "lon": 82.9204},
    {"key": "yak", "name": "Якутск",      "lat": 62.0355,  "lon": 129.6755},
]
WALKER_SPAWN_STATION = "nsk"     # база спавна — вокзал Новосибирска
WALKER_SPAWN_KM = 100.0          # человечки появляются в ~100 км от вокзала (к северу)


def walker_area_ok(lat: float, lon: float) -> bool:
    return sifa_area_ok(WALKER_AREA, lat, lon)


def _walker_land_point(lat: float, lon: float):
    """Ближайшая к (lat, lon) точка СУШИ по маске (для вокзалов у побережья)."""
    if sifa_is_land(lat, lon):
        return round(lat, 6), round(lon, 6)
    for r in range(1, 40):
        for dr in range(-r, r + 1):
            for dc in (-r, r):
                tlat, tlon = lat + dr * 0.25, lon + dc * 0.25
                if sifa_is_land(tlat, tlon):
                    return round(tlat, 6), round(tlon, 6)
    return None


WALKER_FORD_MAX = 4   # сколько ВОДНЫХ клеток подряд можно пройти «вброд» (переправа)


def walker_land_route(lat1, lon1, lat2, lon2):
    """Маршрут по суше в пределах WALKER_AREA: поворотные точки [[lat, lon], ...] —
    без стартовой, с финишной. До WALKER_FORD_MAX водных клеток подряд разрешено
    (узкие перешейки/проливы, например Чукотка↔материк). None — пути нет."""
    step = 0.25
    lat0, lon0 = WALKER_AREA[0], WALKER_AREA[1]
    rows = int((WALKER_AREA[2] - lat0) / step) + 1
    cols = int(((WALKER_AREA[3] - lon0) % 360.0) / step) + 1

    def cell_of(lat, lon):
        r = min(rows - 1, max(0, int((lat - lat0) / step)))
        u = (lon - lon0) % 360.0
        c = min(cols - 1, int(u / step))
        return r, c

    def center_of(r, c):
        return lat0 + (r + 0.5) * step, ((lon0 + (c + 0.5) * step + 180.0) % 360.0) - 180.0

    def land_cell(r, c):
        clat, clon = center_of(r, c)
        return sifa_is_land(clat, clon)

    r1, c1 = cell_of(lat1, lon1)
    r2, c2 = cell_of(lat2, lon2)
    if (r1, c1) == (r2, c2):
        return [[round(lat2, 6), round(lon2, 6)]]
    if not land_cell(r2, c2):
        return None
    n = rows * cols
    nrun = WALKER_FORD_MAX + 1          # состояние = клетка + число подряд идущих водных клеток на пути к ней
    start = r1 * cols + c1
    goal = r2 * cols + c2
    def sid(idx, run):
        return idx * nrun + run
    # A* по километражу между центрами клеток: диагональ дороже горизонтали/вертикали,
    # поэтому путь идёт прямо, а не зигзагом (обычный BFS по шагам «дорисовывал» ~2x километраж).
    # Водная клетка проходима «вброд», но с большим штрафом (не более WALKER_FORD_MAX подряд).
    start_c = center_of(r1, c1)
    prev = array('i', [-2]) * (n * nrun)
    gdist = array('d', [1e18]) * (n * nrun)   # float64! float32 округляет вниз, и stale-check губит валидные состояния
    hq = []
    _heap_counter = [0]
    def hpush(item):
        heapq.heappush(hq, item)
    hpush((haversine_km(start_c[0], start_c[1], lat2, lon2), 0.0, 0, sid(start, 0)))
    gdist[sid(start, 0)] = 0.0
    prev[sid(start, 0)] = -1
    found_state = -1
    while hq:
        _, g, _, cs = heapq.heappop(hq)
        if g > gdist[cs] + 1e-6:
            continue
        cur, run = divmod(cs, nrun)
        if cur == goal:
            found_state = cs
            break
        cr, cc = divmod(cur, cols)
        for dr in (-1, 0, 1):
            for dc in (-1, 0, 1):
                if not dr and not dc:
                    continue
                nr, nc = cr + dr, cc + dc
                if nr < 0 or nr >= rows or nc < 0 or nc >= cols:
                    continue
                ni = nr * cols + nc
                # стартовую клетку пропускаем даже если маска промахнулась
                water = not land_cell(nr, nc) and ni != start
                nrun_next = run + 1 if water else 0
                if nrun_next > WALKER_FORD_MAX:
                    continue
                nlat, nlon = center_of(nr, nc)
                clat, clon = center_of(cr, cc)
                w = haversine_km(clat, clon, nlat, nlon)
                if water:
                    w *= 5.0
                ng = g + w
                ns = sid(ni, nrun_next)
                if ng < gdist[ns]:
                    gdist[ns] = ng
                    prev[ns] = cs
                    _heap_counter[0] += 1
                    hpush((ng + haversine_km(nlat, nlon, lat2, lon2), ng, _heap_counter[0], ns))
    if found_state < 0:
        return None
    cells = []
    cs = found_state
    while cs != -1:
        cur, _ = divmod(cs, nrun)
        cells.append(cur)
        cs = prev[cs]
    cells.reverse()
    pts = []
    for i in range(1, len(cells)):
        pr, pc = divmod(cells[i - 1], cols)
        r, c = divmod(cells[i], cols)
        d = (r - pr, c - pc)
        if i == len(cells) - 1:
            pts.append([round(lat2, 6), round(lon2, 6)])
        else:
            nr, nc = divmod(cells[i + 1], cols)
            if (nr - r, nc - c) != d:
                clat, clon = center_of(r, c)
                pts.append([round(clat, 6), round(clon, 6)])
    return pts


def _walker_route_km(lat1, lon1, pts) -> float:
    total = 0.0
    alat, alon = lat1, lon1
    for wp in pts:
        total += haversine_km(alat, alon, wp[0], wp[1])
        alat, alon = wp[0], wp[1]
    return total


def walker_progress(w: dict) -> bool:
    """Продвинуть следопыта по маршруту (лениво). True — прибыл (энергия списана)."""
    if not w.get("route"):
        return False
    now = time.time()
    traveled_km = (now - w["nav_ts"]) / 60.0 * WALKER_SPEED_KM_PER_MIN
    total_km = _walker_route_km(w["nav_from_lat"], w["nav_from_lon"], w["route"])
    alat, alon = w["nav_from_lat"], w["nav_from_lon"]
    left = traveled_km
    for wp in w["route"]:
        seg = haversine_km(alat, alon, wp[0], wp[1])
        if seg <= 0:
            alat, alon = wp[0], wp[1]
            continue
        if left < seg:
            f = left / seg
            w["lat"] = round(alat + (wp[0] - alat) * f, 6)
            w["lon"] = round(alon + (wp[1] - alon) * f, 6)
            return False
        left -= seg
        alat, alon = wp[0], wp[1]
    w["lat"], w["lon"] = round(alat, 6), round(alon, 6)
    w["energy"] = max(0.0, w.get("energy", 0.0) - total_km)
    w["route"] = None
    w["nav_from_lat"] = w["nav_from_lon"] = None
    w["ts"] = now
    return True


# ---------- Поиск клада: клад на суше России, подсказки каждые 12 ч, жизнь 7 дней ----------
KLAD_FILE = "klad.json"
KLAD_LIFE_SEC = 7 * 86400          # неделя — потом сгорает и зарывается новый
KLAD_HINT_STEP_SEC = 12 * 3600
KLAD_FIND_KM = 30.0                # радиус находки от зарытой точки
klad_state = {}
klad_lock = threading.Lock()


def _klad_random_point():
    """Случайная точка СУШИ в пределах территории следопыта."""
    for _ in range(80):
        lat = random.uniform(WALKER_AREA[0] + 1.0, WALKER_AREA[2] - 1.0)
        u = random.uniform(WALKER_AREA[1], WALKER_AREA[3])
        lon = u - 360.0 if u > 180.0 else u
        p = _walker_land_point(lat, lon)
        if p:
            return p
    return None


def klad_new(chat_id: int, save: bool = True):
    """Зарыть новый клад: случайная суша + нарастающие подсказки. Счётчик находок сохраняется."""
    p = _klad_random_point()
    if not p:
        return None
    lat, lon = p
    now = time.time()
    dists = [haversine_km(lat, lon, s["lat"], s["lon"]) for s in WALKER_STATIONS]
    si = int(min(range(len(dists)), key=lambda j: dists[j]))
    ns = "севернее" if lat >= 60.0 else "южнее"
    ew = "восточнее" if (((lon - 90.0 + 540.0) % 360.0) - 180.0) > 0 else "западнее"
    hints = [
        [0, "🏴‍☠️ Клад зарыт где-то на суше России! Ищи человечком 🚶 — клад найдётся, если окажешься в 30 км от точки. Повторить подсказки: /klad"],
        [12 * 3600, f"🧭 Широта клада {ns} 60° параллели"],
        [24 * 3600, f"🧭 Долгота клада {ew} 90° восточной долготы"],
        [48 * 3600, f"🚉 Ближайший вокзал: «{WALKER_STATIONS[si]['name']}»"],
        [96 * 3600, f"📏 Клад примерно в {max(1, round(dists[si] / 50) * 50)} км от вокзала «{WALKER_STATIONS[si]['name']}»"],
        [144 * 3600, f"🗺 Широта клада ≈ {lat:.1f}° (погрешность ±0.3°)"],
        [156 * 3600, f"🗺 Долгота клада ≈ {lon:.1f}° (погрешность ±0.5°)"],
    ]
    old = klad_state.get(chat_id) or {}
    entry = {"lat": lat, "lon": lon, "created_ts": now,
             "expires_ts": now + KLAD_LIFE_SEC, "hints": hints,
             "announced": 1,   # стартовая подсказка анонсируется сразу
             "founds": dict(old.get("founds") or {})}
    klad_state[chat_id] = entry
    if save:
        klad_save_to_github(force=True)
    return entry


def klad_ensure(chat_id: int):
    """Клад чата есть и жив? Иначе зарываем новый."""
    now = time.time()
    entry = klad_state.get(chat_id)
    if entry and now < entry["expires_ts"]:
        return entry
    return klad_new(chat_id)


def klad_on_arrival(chat_id: int, mkey: str, w: dict) -> bool:
    """Человечек ТОЛЬКО ЧТО прибыл: в 30 км от клада — находка! Награда и новый клад."""
    if w.get("route"):
        return False
    with klad_lock:
        entry = klad_state.get(chat_id)
        if not entry or time.time() >= entry["expires_ts"]:
            return False
        if haversine_km(w["lat"], w["lon"], entry["lat"], entry["lon"]) > KLAD_FIND_KM:
            return False
        with geo_lock:
            marker = geo_state.get(chat_id, {}).get(mkey) or {}
            marker["poops"] = marker.get("poops", 0) + 10
            marker.setdefault("souvenirs", []).append("🏴‍☠️")
            name = marker.get("name") or mkey
            tid = marker.get("tid")
            stardust_earn(chat_id, mkey, 10)
            geo_save_to_github()
        founds = dict(entry.get("founds") or {})
        founds[mkey] = founds.get(mkey, 0) + 1
        new_entry = klad_new(chat_id, save=False)
        if new_entry:
            new_entry["founds"] = founds
        else:
            klad_state.pop(chat_id, None)
    # сохранение ВНЕ klad_lock: _save_json_to_github сам берёт этот же Lock,
    # а threading.Lock не реентерабелен — сохранение под локом вешало бы поток навсегда
    klad_save_to_github(force=True)
    try:
        who = tg_mention(int(tid), name) if tid else name
        tg_send_message_id(chat_id,
            f"🏴‍☠️ <b>{who}</b> нашёл КЛАД! В сумке: +10 ☄️ ЗП, +10 💗 и сувенир 🏴‍☠️. "
            "Старый клад выкопан — на карте зарыт НОВЫЙ, поиск начался заново!",
            html_mode=True)
        if new_entry:
            tg_send_message_id(chat_id, new_entry["hints"][0][1])
    except Exception as e:
        print(f"[paint_bot] анонс клада не ушёл: {e!r}", flush=True)
    return True


async def klad_sweep_job(context) -> None:
    """Клад: сгорел (7 дней) — новый; появилась свежая подсказка — анонс в чат."""
    now = time.time()
    with klad_lock:
        items = [(c, e) for c, e in klad_state.items() if e]
    for chat_id, entry in items:
        if now >= entry["expires_ts"]:
            with klad_lock:
                new_entry = klad_new(chat_id, save=False)  # save под klad_lock = самодедлок
            if new_entry:
                klad_save_to_github(force=True)
                tg_send_message_id(chat_id,
                    "⌛ Клад, который никто не нашёл, сгорел в земле… "
                    "Но следопыты уже зарыли НОВЫЙ!\n" + new_entry["hints"][0][1])
            continue
        idx = sum(1 for o, _ in entry["hints"] if entry["created_ts"] + o <= now)
        if idx > int(entry.get("announced", 0)):
            entry["announced"] = idx
            klad_save_to_github(force=True)
            if idx - 1 < len(entry["hints"]):
                tg_send_message_id(chat_id, "🧩 Свежая подсказка о кладе:\n" + entry["hints"][idx - 1][1])


_klad_last_save = 0.0


def klad_save_to_github(force: bool = False) -> None:
    global _klad_last_save
    if not geo_token():
        return
    now = time.time()
    if not force and now - _klad_last_save < SIFA_SAVE_INTERVAL_SEC:
        return
    _klad_last_save = now
    _save_json_to_github(KLAD_FILE, klad_state, klad_lock, "klad")


def klad_load_from_github() -> None:
    loaded = _load_json_from_github(KLAD_FILE, "klad")
    if loaded:
        for cid, entry in loaded.items():
            klad_state[int(cid)] = entry
        print(f"[paint_bot] klad: загружено {len(loaded)} чатов из Git", flush=True)


# ---------- Корабли (Галеоны): верфь, плавание, абордаж и КНБ ----------
SHIP_COST_WOOD = 10            # постройка Галеона на верфи — 10 дерева
SHIP_SPEED_KM_PER_MIN = 5000.0 # скорость корабля
SHIP_BOARD_KM = 500.0          # сближение на эту дистанцию → доступен Абордаж
SHIP_PICK_SEC = 5              # окно выбора в КНБ (после готовности обоих)
SHIP_PICK_GRACE_SEC = 3        # сетевая грация к окну выбора
SHIP_ROUNDEND_SEC = 4          # пауза «раунд окончен» перед следующим раундом
SHIP_READY_TIMEOUT = 180       # дуэль отменяется, если оба не нажали «Готов»
SHIP_CPU_AFTER_SEC = 180       # неявившийся капитан заменяется командой (компьютером)
SHIP_DUEL_KEEP_SEC = 600       # финальный экран дуэли хранится столько после боя
SHIP_REBUILD_DELAY_SEC = 600   # пауза: новый Галеон не ранее чем через 10 мин после потопления

# ---------- Водный маршрут Галеона: обход суши по битовой маске ----------
# Та же сетка, что у sifa_is_land: 720×1440 клеток по 0.25° (Natural Earth 50m).
# Маску НЕ утолщаем дополнительно — между клетками-суходолами корабль
# может «протекать» (согласовано с владельцем).
SHIP_ROUTE_ROWS = 720
SHIP_ROUTE_COLS = 1440

def _ship_cell(lat, lon):
    r = min(SHIP_ROUTE_ROWS - 1, max(0, int((90.0 - lat) * 4)))
    c = min(SHIP_ROUTE_COLS - 1, max(0, int((lon + 180.0) * 4)))
    return r, c

def _ship_cell_water(r, c):
    return not bool((_sifa_land[r * 180 + (c >> 3)] >> (7 - (c & 7))) & 1)

def _ship_cell_center(r, c):
    return 90.0 - (r + 0.5) * 0.25, -180.0 + (c + 0.5) * 0.25

def ship_water_route(lat1, lon1, lat2, lon2):
    """Маршрут только по воде: поворотные точки [[lat, lon], ...] — без стартовой,
    с финишной. Корабль плывёт по ломаной и сам огибает сушу.
    None — водного пути нет (точка в недостижимом водоёме)."""
    r1, c1 = _ship_cell(lat1, lon1)
    r2, c2 = _ship_cell(lat2, lon2)
    if (r1, c1) == (r2, c2):
        return [[round(lat2, 6), round(lon2, 6)]]
    if not _ship_cell_water(r2, c2):
        return None
    n = SHIP_ROUTE_ROWS * SHIP_ROUTE_COLS
    prev = array('i', [-2]) * n          # -2 = не посещена, -1 = старт, иначе индекс prev
    start = r1 * SHIP_ROUTE_COLS + c1
    goal = r2 * SHIP_ROUTE_COLS + c2
    prev[start] = -1
    dq = deque([start])
    found = False
    while dq:
        cur = dq.popleft()
        if cur == goal:
            found = True
            break
        cr, cc = divmod(cur, SHIP_ROUTE_COLS)
        for dr in (-1, 0, 1):
            for dc in (-1, 0, 1):
                if not dr and not dc:
                    continue
                nr, nc = cr + dr, cc + dc
                if nr < 0 or nr >= SHIP_ROUTE_ROWS or nc < 0 or nc >= SHIP_ROUTE_COLS:
                    continue
                ni = nr * SHIP_ROUTE_COLS + nc
                if prev[ni] != -2:
                    continue
                # стартовую клетку пропускаем даже если она суша (корабль уже там стоит);
                # остальные — строго по воде
                if ni != start and not _ship_cell_water(nr, nc):
                    continue
                prev[ni] = cur
                dq.append(ni)
    if not found:
        return None
    cells = []
    cur = goal
    while cur != -1:
        cells.append(cur)
        cur = prev[cur]
    cells.reverse()
    # оставляем только точки излома (смена направления), финиш — точная цель
    pts = []
    for i in range(1, len(cells)):
        pr, pc = divmod(cells[i - 1], SHIP_ROUTE_COLS)
        r, c = divmod(cells[i], SHIP_ROUTE_COLS)
        d = (r - pr, c - pc)
        if i == len(cells) - 1:
            pts.append([round(lat2, 6), round(lon2, 6)])
        else:
            nr, nc = divmod(cells[i + 1], SHIP_ROUTE_COLS)
            if (nr - r, nc - c) != d:
                clat, clon = _ship_cell_center(r, c)
                pts.append([round(clat, 6), round(clon, 6)])
    return pts
# ---------- Морской Рынок: локация в океане (Карское море, 79°N 70°E) ----------
MARKET_LAT, MARKET_LON = 79.0, 70.0   # позиция одинакова для всех чатов, владелец — свой на чат
MARKET_GIFT_COST = 5                  # обмен: 5 открытых подарков -> +1 ЗП, +1 дерева, +1 какашка
MARKET_FILE = "market.json"
# потопленные корабли с карты не исчезают: висят «мемориальными рифами»,
# пока капитан не спустит на воду новый Галеон (запись перезаписывается)

# Картинки маркеров (base64, PNG ~256px, прозрачный фон) — встраиваются скриптом
GALLEON_B64 = "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"
GALLEON_SUNK_B64 = "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"

SHIPS_FILE = "ships.json"
ships_state = {}   # f"{chat}|{user}" -> {"chat","user","name","lat","lon","to_lat","to_lon",
                   #  "nav_from_lat","nav_from_lon","nav_ts","route","sunk","sunk_ts"}
                   #  route — поворотные точки водного маршрута [[lat,lon],...] или None
ship_duels = {}    # duel_id -> дуэль КНБ; хранится в ship_duels.json — бой переживает рестарт

SHIP_SINK_PHRASES = [
    "крабы уже разбирают меню 🦀",
    "рыбам теперь есть с чем фоткаться 🐟",
    "адмирал слегка переоценил свои таланты 🏴‍☠️",
]
RPS_NAMES = {"r": "🪨 Камень", "s": "✂️ Ножницы", "p": "📜 Бумага"}
RPS_BEATS = {"r": "s", "s": "p", "p": "r"}


def ship_key(chat_id: int, user: str) -> str:
    return f"{chat_id}|{user}"


def ship_of(chat_id: int, user: str, name: str = ""):
    """Корабль игрока: по ключу, иначе через метку (tid/имя)."""
    sh = ships_state.get(ship_key(chat_id, user))
    if sh is not None:
        return sh
    mkey = resolve_marker_key(chat_id, user, name)
    if mkey:
        return ships_state.get(ship_key(chat_id, mkey))
    return None


def ships_save_to_github() -> None:
    _save_json_to_github(SHIPS_FILE, ships_state, geo_lock, "ships")


def ships_load_from_github() -> None:
    loaded = _load_json_from_github(SHIPS_FILE, "ships")
    if loaded:
        ships_state.update(loaded)
        print(f"[paint_bot] ships: загружено {len(loaded)} кораблей", flush=True)


market_state = {}   # str(chat_id) -> {"owner": mkey|None, "owner_name": str, "captured_ts": float}
                    # владелец Морского Рынка чата; None/"свободен" — пока никто не захватывал


def market_save_to_github() -> None:
    _save_json_to_github(MARKET_FILE, market_state, geo_lock, "market")


def market_load_from_github() -> None:
    loaded = _load_json_from_github(MARKET_FILE, "market")
    if loaded:
        # в JSON ключи становятся строками — в памяти ключи int (chat_id),
        # без нормализации после перезапуска владелец рынка терялся
        market_state.update({int(cid): e for cid, e in loaded.items()})
        print(f"[paint_bot] market: загружено {len(loaded)} рынков", flush=True)


DUELS_FILE = "ship_duels.json"


def duels_save_to_github() -> None:
    """Активные и недавно завершённые дуэли — чтобы рестарт сервера не сбрасывал бой."""
    _save_json_to_github(DUELS_FILE, ship_duels, geo_lock, "duels")


def duels_load_from_github() -> None:
    loaded = _load_json_from_github(DUELS_FILE, "duels")
    if loaded:
        ship_duels.update(loaded)
        print(f"[paint_bot] duels: загружено {len(loaded)} дуэлей", flush=True)


# Мемориальные рифы: потопленные корабли, снятые с учёта при перестройке.
# Живут отдельно от боевых кораблей — на карте видны всем, в игре не участвуют.
WRECKS_FILE = "wrecks.json"
wrecks_state = {}


def wrecks_save_to_github() -> None:
    _save_json_to_github(WRECKS_FILE, wrecks_state, geo_lock, "wrecks")


def wrecks_load_from_github() -> None:
    loaded = _load_json_from_github(WRECKS_FILE, "wrecks")
    if loaded:
        wrecks_state.update(loaded)
        print(f"[paint_bot] wrecks: загружено {len(loaded)} рифов", flush=True)


def ship_in_duel(chat_id: int, user: str):
    """Активная дуэль (ready/pick/roundend). Завершённые сюда не входят —
    корабль свободен сразу после боя, даже пока финальный экран ещё показывается."""
    for d in ship_duels.values():
        if d["chat"] == chat_id and user in (d["a"], d["b"]) and d["phase"] != "finished":
            return d
    return None


def duel_view_for(chat_id: int, user: str, now: float):
    """Дуэль для показа игроку: активная или завершённая в окне показа финала."""
    d = ship_in_duel(chat_id, user)
    if d is not None:
        duel_tick(d, now)
        return ship_in_duel(chat_id, user) or finished_duel_for(chat_id, user, now)
    return finished_duel_for(chat_id, user, now)


def finished_duel_for(chat_id: int, user: str, now: float):
    for dd in ship_duels.values():
        if (dd["chat"] == chat_id and user in (dd["a"], dd["b"])
                and dd["phase"] == "finished"
                and user not in dd.get("seen_by", [])
                and now - dd.get("finished_ts", 0) <= SHIP_DUEL_KEEP_SEC):
            return dd
    return None


def duel_cleanup(now: float) -> None:
    """Выбросить завершённые дуэли, которые уже показаны."""
    stale = [k for k, dd in ship_duels.items()
             if dd["phase"] == "finished"
             and now - dd.get("finished_ts", 0) > SHIP_DUEL_KEEP_SEC]
    for did in stale:
        ship_duels.pop(did, None)
    if stale:
        duels_save_to_github()


def ship_progress(sh: dict) -> bool:
    """Продвинуть корабль по маршруту (лениво). Вернуть True, если прибыл (для сохранения)."""
    if sh.get("sunk") or sh.get("to_lat") is None:
        return False
    if ship_in_duel(sh["chat"], sh["user"]):
        return False                       # в бою корабль стоит
    now = time.time()
    traveled_km = (now - sh["nav_ts"]) / 60.0 * SHIP_SPEED_KM_PER_MIN
    route = sh.get("route")
    if route:
        # движение вдоль водной ломаной: позиция — на расстоянии traveled_km от старта
        alat, alon = sh["nav_from_lat"], sh["nav_from_lon"]
        left = traveled_km
        for wp in route:
            seg = haversine_km(alat, alon, wp[0], wp[1])
            if seg <= 0:
                alat, alon = wp[0], wp[1]
                continue
            if left < seg:
                f = left / seg
                sh["lat"] = round(alat + (wp[0] - alat) * f, 6)
                sh["lon"] = round(alon + (wp[1] - alon) * f, 6)
                return False              # промежуточная позиция пересчитывается, не сохраняем
            left -= seg
            alat, alon = wp[0], wp[1]
        sh["lat"], sh["lon"] = sh["to_lat"], sh["to_lon"]
        sh["to_lat"] = sh["to_lon"] = None
        sh["nav_from_lat"] = sh["nav_from_lon"] = None
        sh["route"] = None
        return True
    # старые корабли без маршрута — прямая, как раньше
    total = haversine_km(sh["nav_from_lat"], sh["nav_from_lon"], sh["to_lat"], sh["to_lon"])
    elapsed_min = (now - sh["nav_ts"]) / 60.0
    if total <= 0 or elapsed_min * SHIP_SPEED_KM_PER_MIN >= total:
        sh["lat"], sh["lon"] = sh["to_lat"], sh["to_lon"]
        sh["to_lat"] = sh["to_lon"] = None
        sh["nav_from_lat"] = sh["nav_from_lon"] = None
        return True
    frac = (elapsed_min * SHIP_SPEED_KM_PER_MIN) / total
    sh["lat"] = round(sh["nav_from_lat"] + (sh["to_lat"] - sh["nav_from_lat"]) * frac, 6)
    sh["lon"] = round(sh["nav_from_lon"] + (sh["to_lon"] - sh["nav_from_lon"]) * frac, 6)
    return False                          # промежуточная позиция пересчитывается, не сохраняем


def _rps_winner(pa, pb):
    """Кто выиграл раунд КНБ: 'a', 'b' или None (ничья). Ходы сюда приходят всегда
    заполненные — таймаут уже заменён случайным выбором в duel_tick."""
    if pa == pb:
        return None
    return "a" if RPS_BEATS[pa] == pb else "b"


def spectator_duel(d: dict) -> dict:
    """Нейтральный вид дуэли для зрителя: чужие ходы в раунде скрыты,
    итоги прошлых раундов и финал — открыты."""
    na, nb = duel_display_names(d)
    out = {
        "id": d["id"], "phase": d["phase"], "round": d["round"],
        "a_name": na, "b_name": nb,
        "cpu_name": (na if d.get("cpu") == "a" else nb) if d.get("cpu") else None,
        "wins_a": d["wins"]["a"], "wins_b": d["wins"]["b"],
        "a_ready": d["a"] in d["ready"], "b_ready": d["b"] in d["ready"],
        "a_picked": d["pa"] is not None, "b_picked": d["pb"] is not None,
        "pick_left": max(0, int(d.get("pick_deadline", 0) - time.time())),
        "wait_left": (max(0, int(d["ts"] + SHIP_CPU_AFTER_SEC - time.time()))
                      if d["phase"] == "ready" else 0),
    }
    if d.get("last"):
        out["last"] = {"round": d["last"]["round"],
                       "pa": d["last"]["pa"], "pb": d["last"]["pb"],
                       "winner": d["last"]["winner"]}
    if d["phase"] == "finished":
        out["loser_name"] = na if d["loser_side"] == "a" else nb
        out["sink_phrase"] = d["sink_phrase"]
    return out


def _finish_duel(d: dict) -> None:
    winner = "a" if d["wins"]["a"] > d["wins"]["b"] else "b"
    loser = "b" if winner == "a" else "a"
    na, nb = duel_display_names(d)
    dn = {"a": na, "b": nb}
    lsh = ships_state.get(ship_key(d["chat"], d[loser]))
    wsh = ships_state.get(ship_key(d["chat"], d[winner]))
    phrase = random.choice(SHIP_SINK_PHRASES)
    if lsh is not None:
        lsh["sunk"] = True
        lsh["sunk_ts"] = time.time()
        lsh["to_lat"] = lsh["to_lon"] = None
        lsh["nav_from_lat"] = lsh["nav_from_lon"] = None
        lsh["route"] = None
    if wsh is not None:
        wsh["wins"] = wsh.get("wins", 0) + 1   # статистика живёт на корабле — с ним тонет
    lmarker = geo_state.get(d["chat"], {}).get(d[loser])
    if lmarker is not None:
        lmarker["ships_lost"] = lmarker.get("ships_lost", 0) + 1   # а это навсегда у капитана
    wmarker = geo_state.get(d["chat"], {}).get(d[winner])
    if wmarker is not None:
        wmarker["ships_won"] = wmarker.get("ships_won", 0) + 1     # потопленные галеоны — навсегда
    d["phase"] = "finished"
    d["finished_ts"] = time.time()
    d["loser_side"], d["winner_side"] = loser, winner
    d["sink_phrase"] = phrase
    ships_save_to_github()
    geo_save_to_github()
    duels_save_to_github()
    if d.get("cpu"):
        note = (f"Капитан {dn[d['cpu']]} не явился на абордаж — "
                f"команда билась сама, без единой капитанской пощады! ")
    else:
        note = ""
    try:
        tg_send_with_cleanup(
            d["chat"],
            f"⚔️ АБОРДАЖ ОКОНЧЕН! {note}Корабль капитана "
            f"{geo_mention(d['chat'], d[loser], dn[loser])} был потоплен — {phrase} "
            f"Победил капитан {geo_mention(d['chat'], d[winner], dn[winner])} 🏆",
            600,
            html_mode=True,
        )
    except Exception as e:
        print(f"[paint_bot] уведомление о потоплении не ушло: {e!r}", flush=True)


def _duel_enter_pick(d: dict, now: float) -> None:
    d["phase"] = "pick"
    d["pick_deadline"] = now + SHIP_PICK_SEC + SHIP_PICK_GRACE_SEC
    if d.get("cpu"):
        # команда (компьютер) думает над ходом пару секунд — по-человечески
        d["cpu_pick_at"] = now + random.uniform(1.5, 4.5)


def duel_tick(d: dict, now: float) -> None:
    """Лениво продвинуть дуэль КНБ (вызывается из /geodata и /shipduel).
    Каждая смена фазы/раунда сохраняется в GitHub — рестарт сервера (деплой,
    падение Render) продолжит бой с того же раунда и счёта, а не с нуля."""
    if d["phase"] == "ready":
        if len(d["ready"]) >= 2:
            _duel_enter_pick(d, now)
            duels_save_to_github()
        elif len(d["ready"]) == 1 and now - d["ts"] > SHIP_CPU_AFTER_SEC:
            # второй капитан не явился за 3 минуты — вместо него дерётся его команда
            human = d["a"] if d["a"] in d["ready"] else d["b"]
            d["cpu"] = "b" if human == d["a"] else "a"   # сторона капитана
            d["ready"] = [d["a"], d["b"]]
            logline(f"ship duel: капитан {d[d['cpu'] + '_name']} не явился — играет команда")
            duels_save_to_github()
            _duel_enter_pick(d, now)
            duels_save_to_github()
        elif not d["ready"] and now - d["ts"] > SHIP_READY_TIMEOUT:
            ship_duels.pop(d["id"], None)
            duels_save_to_github()
    elif d["phase"] == "pick":
        cpu_side = d.get("cpu")
        if cpu_side and d["p" + cpu_side] is None and now >= d.get("cpu_pick_at", 0):
            d["p" + cpu_side] = random.choice(["r", "s", "p"])
        if (d["pa"] and d["pb"]) or now > d["pick_deadline"]:
            # не успел выбрать — корабельная команда хватает первое попавшееся
            rand_a = not d["pa"]
            rand_b = not d["pb"]
            if rand_a:
                d["pa"] = random.choice(["r", "s", "p"])
            if rand_b:
                d["pb"] = random.choice(["r", "s", "p"])
            w = _rps_winner(d["pa"], d["pb"])
            if w:
                d["wins"][w] += 1
            d["last"] = {"pa": d["pa"], "pb": d["pb"], "winner": w, "round": d["round"],
                         "random": [s for s, r in (("a", rand_a), ("b", rand_b)) if r]}
            d["pa"] = d["pb"] = None
            d["phase"] = "roundend"
            d["roundend_ts"] = now
            duels_save_to_github()
    elif d["phase"] == "roundend":
        if now - d["roundend_ts"] > SHIP_ROUNDEND_SEC:
            if d["wins"]["a"] >= 3 or d["wins"]["b"] >= 3:
                _finish_duel(d)
            else:
                d["round"] += 1
                _duel_enter_pick(d, now)
                duels_save_to_github()
    elif d["phase"] == "finished":
        if now - d["finished_ts"] > SHIP_DUEL_KEEP_SEC:
            ship_duels.pop(d["id"], None)
            duels_save_to_github()


def public_duel(d: dict, user: str) -> dict:
    """Дуэль в безопасном виде для игрока user (без подглядывания чужого выбора)."""
    side = "a" if d["a"] == user else "b"
    other = "b" if side == "a" else "a"
    na, nb = duel_display_names(d)
    dn = {"a": na, "b": nb}
    out = {
        "id": d["id"], "phase": d["phase"], "round": d["round"],
        "my_side": side,
        "cpu_opp": d.get("cpu") == other,
        "opp_name": dn[other], "my_name": dn[side],
        "wins_me": d["wins"][side], "wins_opp": d["wins"][other],
        "ready_me": user in d["ready"], "ready_opp": d[other] in d["ready"],
        "my_pick": d["p" + side], "opp_picked": bool(d["p" + other]),
        "opp_name_full": dn[other],
        "pick_left": max(0, int(d.get("pick_deadline", 0) - time.time())),
        "wait_left": (max(0, int(d["ts"] + SHIP_CPU_AFTER_SEC - time.time()))
                      if d["phase"] == "ready" else 0),
    }
    if d.get("last"):
        last = d["last"]
        w = last["winner"]
        out["last"] = {
            "round": last["round"],
            "my_pick": last["p" + side], "opp_pick": last["p" + other],
            "i_won": (w == side) if w else None,
            "my_random": side in last.get("random", []),
        }
    if d["phase"] == "finished":
        out["i_won"] = d["winner_side"] == side
        out["loser_name"] = dn[d["loser_side"]]
        out["sink_phrase"] = d["sink_phrase"]
    return out


def _sifa_entry(chat_id: int) -> dict:
    """Запись чата в sifa_state: {"ships": {...}, "area": [...]}. Вызывать под sifa_lock."""
    entry = sifa_state.get(chat_id)
    if not (isinstance(entry, dict) and "ships" in entry):
        old = entry if isinstance(entry, dict) else {}
        entry = {"ships": old, "area": None}
        sifa_state[chat_id] = entry
    return entry
sifa_state = {}               # chat_id -> {user_key: {"lat","lon","heading","ts","name"}}
sifa_lock = threading.Lock()
_sifa_last_save = 0.0


walker_state = {}             # chat_id -> {user_key: {"lat","lon","energy","name","tid","route",...}}
walker_lock = threading.Lock()
_walker_last_save = 0.0


def walker_save_to_github(force: bool = False) -> None:
    global _walker_last_save
    if not geo_token():
        return
    now = time.time()
    if not force and now - _walker_last_save < SIFA_SAVE_INTERVAL_SEC:
        return
    _walker_last_save = now
    _save_json_to_github(WALKER_FILE, walker_state, walker_lock, "walker")


def walker_load_from_github() -> None:
    loaded = _load_json_from_github(WALKER_FILE, "walker")
    if loaded:
        total = 0
        for cid, ships in loaded.items():
            walker_state[int(cid)] = ships
            total += len(ships)
        print(f"[paint_bot] walker: загружено {total} следопытов из Git", flush=True)


_walker_station_pts = None


def _walker_station_point(station: dict):
    """Координаты вокзала, подвинутые на ближайшую сушу (кэшируется на процесс)."""
    global _walker_station_pts
    if _walker_station_pts is None:
        _walker_station_pts = {}
        for s in WALKER_STATIONS:
            _walker_station_pts[s["key"]] = _walker_land_point(s["lat"], s["lon"]) \
                or (s["lat"], s["lon"])
    return _walker_station_pts[station["key"]]


def _walker_spawn_point():
    """Точка спавна: ~100 км к северу от вокзала Новосибирск, снап на сушу."""
    st = next(s for s in WALKER_STATIONS if s["key"] == WALKER_SPAWN_STATION)
    blat, blon = _walker_station_point(st)
    return _walker_land_point(blat + WALKER_SPAWN_KM / 111.32, blon) or (blat, blon)


def _walker_spawn(name: str, tid: str) -> dict:
    """Новый следопыт: старт в 100 км от вокзала Новосибирск, энергия полная."""
    lat, lon = _walker_spawn_point()
    w = {"lat": lat, "lon": lon, "energy": WALKER_ENERGY_MAX,
         "name": name, "route": None, "nav_from_lat": None, "nav_from_lon": None,
         "nav_ts": 0.0, "ts": time.time()}
    if tid and str(tid).isdigit():
        w["tid"] = tid
    return w


def apply_walker_reloc_2026_11_09() -> None:
    """Разовый перенос (2026-11-09): все человечки — на точку спавна
    (в 100 км от вокзала Новосибирск), Sumai — на вокзал Брянска. Маршруты сброшены."""
    tag = "walker_reloc_2026-11-09"
    if meteor_credits.get(tag):
        return
    meteor_credits[tag] = True
    spawn = _walker_spawn_point()
    bry = next(s for s in WALKER_STATIONS if s["key"] == "bry")
    bry_pt = _walker_station_point(bry)
    moved = 0
    with walker_lock:
        for walkers in walker_state.values():
            for k, w in walkers.items():
                lat, lon = bry_pt if k == "Sumai" else spawn
                w["lat"], w["lon"] = round(lat, 6), round(lon, 6)
                w["route"] = None
                w["nav_from_lat"] = w["nav_from_lon"] = None
                w["nav_ts"] = 0.0
                w["ts"] = time.time()
                moved += 1
    if moved:
        walker_save_to_github(force=True)
    logline(f"walker reloc: перенесено {moved} человечек (Sumai -> Брянск)")
    meteor_save_to_github()


def sifa_save_to_github(force: bool = False) -> None:
    global _sifa_last_save
    if not geo_token():
        return
    now = time.time()
    if not force and now - _sifa_last_save < SIFA_SAVE_INTERVAL_SEC:
        return
    _sifa_last_save = now
    _save_json_to_github(SIFA_FILE, sifa_state, sifa_lock, "sifa")


def sifa_load_from_github() -> None:
    loaded = _load_json_from_github(SIFA_FILE, "sifa")
    if loaded:
        total = 0
        for cid, entry in loaded.items():
            if not (isinstance(entry, dict) and "ships" in entry):
                entry = {"ships": entry if isinstance(entry, dict) else {}, "area": None}
            sifa_state[int(cid)] = entry
            total += len(entry["ships"])
        print(f"[paint_bot] sifa: загружено {total} кораблей из Git", flush=True)
    # Разовый фикс 2026-11-02: касатка ПМ застряла на западной границе —
    # сдвигаем её на 3000 км восточнее (применится один раз, пока lon < -150).
    try:
        _pm = sifa_state.get(-1002304715333, {}).get("ships", {}).get("ПМ")
        if _pm is not None and _pm.get("lon", 0) < -150:
            _pm["lon"] = max(-180.0, min(180.0, _pm["lon"] + 3000.0 / (111.32 * math.cos(math.radians(_pm["lat"])))))
            _pm["ts"] = time.time()
            print(f"[paint_bot] sifa: разовый сдвиг касатки ПМ -> lon {_pm['lon']:.2f}", flush=True)
    except Exception:
        pass


def submarine_save_to_github() -> None:
    payload = {"submarines": {str(k): v for k, v in submarine_state.items()},
               "gifts": gifts_state}
    _save_json_to_github(SUBMARINE_FILE, payload, geo_lock, "submarine")


def submarine_load_from_github() -> None:
    loaded = _load_json_from_github(SUBMARINE_FILE, "submarine")
    if not loaded:
        return
    submarine_state.update({int(cid): s for cid, s in loaded.get("submarines", {}).items()})
    gifts_state.update(loaded.get("gifts", {}))
    print(f"[paint_bot] submarine: лодок {len(submarine_state)}, подарков {len(gifts_state)}", flush=True)


# ---------- Остров: сохранение и помощники ----------

def islands_save_to_github() -> None:
    _save_json_to_github(ISLAND_FILE, islands_state, geo_lock, "islands")


def islands_load_from_github() -> None:
    loaded = _load_json_from_github(ISLAND_FILE, "islands")
    if loaded:
        islands_state.update(loaded)
        print(f"[paint_bot] islands: загружено {len(loaded)} островов из Git", flush=True)


def island_level(isl: dict) -> int:
    return min(ISLAND_MAX_LEVEL, 1 + isl.get("xp", 0) // ISLAND_XP_PER_LEVEL)


def plane_speed_km_per_min(chat_id) -> float:
    """Скорость самолёта: в Песочнице — тестовая (1000 км за 10 секунд)."""
    return SANDBOX_FAST_KM_PER_MIN if chat_id == GEO2_CHAT_ID else PLANE_SPEED_KM_PER_MIN


def island_plane_progress(guest: dict):
    """Текущая позиция самолёта (по прямой) и флаг прибытия."""
    total = haversine_km(guest["from_lat"], guest["from_lon"],
                         guest["to_lat"], guest["to_lon"])
    elapsed_min = (time.time() - guest["start_ts"]) / 60.0
    done_km = min(elapsed_min * plane_speed_km_per_min(guest.get("chat") or 0), total)
    frac = done_km / total if total > 0 else 1.0
    lat = guest["from_lat"] + (guest["to_lat"] - guest["from_lat"]) * frac
    lon = guest["from_lon"] + (guest["to_lon"] - guest["from_lon"]) * frac
    return lat, lon, total <= 0 or done_km >= total


def island_guest_at(chat_id: int, user: str):
    """Остров, на котором user сейчас гостит (leg='staying'), или None."""
    for isl in islands_state.values():
        if isl["chat"] != chat_id:
            continue
        g = isl.get("guest")
        if g and g["user"] == user and g["leg"] == "staying":
            return isl
    return None


def island_of(chat_id: int, user: str, name: str = ""):
    """Остров чата, где user — владелец (основной или совладелец), или None.
    Мягкий матчинг: ключ владельца, запомненный tid или имя его метки."""
    mkey = resolve_marker_key(chat_id, user, name) if name else None
    for isl in islands_state.values():
        if isl["chat"] != chat_id or isl.get("banned"):
            continue
        owners = isl.get("owners") or [isl["owner"]]
        if user in owners or (mkey is not None and mkey in owners):
            return isl
    return None


def stardust_get(chat_id: int, user: str) -> int:
    return stardust_state.get(f"{chat_id}|{user}", 0)


def stardust_keys(chat_id: int, user: str, name: str = "") -> list:
    """Ключи баланса ЗП пользователя: по переданному ключу + по метке (tid/имя) —
    чтобы браузерная игра (ключ = имя) и Telegram (ключ = числовой id) делили один баланс."""
    keys = [f"{chat_id}|{user}"]
    try:
        mkey = resolve_marker_key(chat_id, user, name)
    except Exception:
        mkey = None
    if mkey:
        alt = f"{chat_id}|{mkey}"
        if alt not in keys:
            keys.append(alt)
    return keys


def stardust_balance(chat_id: int, user: str, name: str = "") -> int:
    return sum(stardust_state.get(k, 0) for k in stardust_keys(chat_id, user, name))


def stardust_earn(chat_id: int, user: str, amount: int, name: str = "") -> int:
    """Начислить ЗП на канонический баланс (ключ метки). Вернуть новый баланс."""
    keys = stardust_keys(chat_id, user, name)
    key = keys[-1]
    stardust_state[key] = stardust_state.get(key, 0) + amount
    return stardust_state[key]


def stardust_spend(chat_id: int, user: str, amount: int, name: str = ""):
    """Списать ЗП (сначала с переданного ключа, затем с ключа метки).
    Вернуть остаток баланса или None, если не хватает."""
    keys = stardust_keys(chat_id, user, name)
    if sum(stardust_state.get(k, 0) for k in keys) < amount:
        return None
    left = amount
    for k in keys:
        have = stardust_state.get(k, 0)
        take = min(have, left)
        if take:
            stardust_state[k] = have - take
            left -= take
        if not left:
            break
    return sum(stardust_state.get(k, 0) for k in keys)


def meteor_check(chat_id: int):
    """Проверить/обновить состояние метеоритов чата.
    Вернуть (свежий активный метеорит или None, только что упал — bool, что-то изменилось — bool)."""
    now = time.time()
    changed = False
    m = meteor_state.get(chat_id)
    if m is None:
        m = {"current": None, "craters": [], "next_fall": 0.0}
        meteor_state[chat_id] = m
        changed = True
    cur = m.get("current")
    if cur is not None and now - cur["fall_ts"] >= METEOR_LIFETIME_SEC:
        # окно сбора закрылось: метеорит сразу исчезает с карты (воронки не остаются)
        m["current"] = None
        changed = True
    fell = False
    if m.get("current") is None and now >= m.get("next_fall", 0.0):
        lat, lon = random_point_anywhere()  # зона падения — вся карта
        m["current"] = {"lat": lat, "lon": lon, "fall_ts": now, "taken": False}
        m["next_fall"] = now + METEOR_PERIOD_SEC + random.uniform(0, 3000)
        fell = True
        changed = True
    return m.get("current"), fell, changed


async def meteor_fall_job(context) -> None:
    """Фоновая проверка раз в минуту: падение метеоритов + уведомление в чат."""
    for chat_id in ALLOWED_GROUPS:
        with geo_lock:
            cur, fell, changed = meteor_check(chat_id)
        if changed:
            meteor_save_to_github()
        if not fell:
            continue
        try:
            msg = await context.bot.send_message(chat_id, METEOR_NOTIFY_TEXT)
            schedule_event_cleanup(context, chat_id, msg.message_id, METEOR_LIFETIME_SEC)
            logline(f"meteor fell chat={chat_id} lat={cur['lat']:.2f} lon={cur['lon']:.2f} +notify")
        except Exception as e:
            logline(f"meteor fell chat={chat_id}, но уведомление не ушло: {e!r}")


def saga_save_to_github() -> None:
    _save_json_to_github(SAGA_FILE, saga_state, geo_lock, "saga")


def saga_load_from_github() -> None:
    loaded = _load_json_from_github(SAGA_FILE, "saga")
    if loaded:
        saga_state.update({int(cid): s for cid, s in loaded.items()})
        print(f"[paint_bot] saga: загружено {len(loaded)} саг из Git", flush=True)


async def saga_publish(bot, chat_id: int) -> None:
    """Опубликовать эпос в чат (частями, если длинно) и стереть сагу."""
    s = saga_state.pop(chat_id, None)
    if s is None:
        return
    saga_save_to_github()
    chapters = s.get("chapters", [])
    if not chapters:
        await bot.send_message(chat_id, "📜 Сага завершена, но в ней не оказалось глав 🙂")
        return
    date = datetime.datetime.now(MSK_TZ).strftime("%d.%m.%Y")
    parts, current = [], ""
    for ch in chapters:
        piece = ch if not current else "\n\n" + ch
        if len(current) + len(piece) > 3800:
            parts.append(current)
            current = ch
        else:
            current += piece
    parts.append(current)
    await bot.send_message(chat_id, f"📜 САГА ЧАТА от {date} — финал! Всего глав: {len(chapters)}")
    for i, part in enumerate(parts):
        header = "📜 (продолжение)\n\n" if i else ""
        await bot.send_message(chat_id, header + part)
    await bot.send_message(
        chat_id,
        "📜 Конец саги! Авторы остались анонимными. Новую можно начать в меню /startsum.",
    )


# ---------- Автобэкап меток и писем ----------

MSK_TZ = datetime.timezone(datetime.timedelta(hours=3))  # московское время (UTC+3, без летнего)
BACKUP_KEEP_DAYS = 14  # сколько дневных снапшотов держать в backups/


def _delete_github_file(filename: str) -> None:
    """Удалить файл из paint-bot-data (молча, если его нет)."""
    if not geo_token():
        return
    try:
        current = json.load(urllib.request.urlopen(geo_github_request("GET", filename), timeout=15))
        req = geo_github_request("DELETE", filename)
        req.data = json.dumps({"message": f"cleanup {filename}", "sha": current["sha"]}).encode("utf-8")
        urllib.request.urlopen(req, timeout=15)
    except urllib.error.HTTPError as e:
        if e.code != 404:
            print(f"[paint_bot] backup cleanup failed for {filename}: {e!r}", flush=True)
    except Exception as e:
        print(f"[paint_bot] backup cleanup failed for {filename}: {e!r}", flush=True)


def backup_geo_data() -> None:
    """Дневной снапшот geo.json и letters.json в paint-bot-data/backups/ — страховка
    от случайного удаления меток: основной geo.json перезаписывается мгновенно,
    а из снапшота можно вернуть состояние за конкретный день."""
    if not geo_token():
        return
    today = datetime.datetime.now(MSK_TZ).strftime("%Y-%m-%d")
    for attempt in range(3):  # GitHub API иногда отваливается по таймауту — повторяем
        ok_geo = _save_json_to_github(f"backups/geo_{today}.json", geo_state, geo_lock, "backup geo")
        ok_letters = _save_json_to_github(f"backups/letters_{today}.json", letters_state, geo_lock, "backup letters")
        _vol_payload = {"volcanoes": {str(k): v for k, v in volcano_state.items()}, "poops": poops_state}
        ok_volcano = _save_json_to_github(f"backups/volcano_{today}.json", _vol_payload, geo_lock, "backup volcano")
        ok_saga = _save_json_to_github(f"backups/saga_{today}.json", saga_state, geo_lock, "backup saga")
        _met_payload = {"meteors": {str(k): v for k, v in meteor_state.items()}, "stardust": stardust_state}
        ok_meteor = _save_json_to_github(f"backups/meteor_{today}.json", _met_payload, geo_lock, "backup meteor")
        _sub_payload = {"submarines": {str(k): v for k, v in submarine_state.items()}, "gifts": gifts_state}
        ok_submarine = _save_json_to_github(f"backups/submarine_{today}.json", _sub_payload, geo_lock, "backup submarine")
        ok_islands = _save_json_to_github(f"backups/islands_{today}.json", islands_state, geo_lock, "backup islands")
        if ok_geo and ok_letters and ok_volcano and ok_saga and ok_meteor and ok_submarine and ok_islands:
            break
        print(f"[paint_bot] backup attempt {attempt + 1} incomplete (geo={ok_geo}, letters={ok_letters}, volcano={ok_volcano}, saga={ok_saga}, meteor={ok_meteor}, submarine={ok_submarine}, islands={ok_islands}), retrying", flush=True)
        time.sleep(5)
    old = (datetime.datetime.now(MSK_TZ) - datetime.timedelta(days=BACKUP_KEEP_DAYS + 1)).strftime("%Y-%m-%d")
    for name in (f"geo_{old}.json", f"letters_{old}.json", f"volcano_{old}.json", f"saga_{old}.json",
                 f"meteor_{old}.json", f"submarine_{old}.json", f"islands_{old}.json"):
        _delete_github_file(f"backups/{name}")
    print(f"[paint_bot] backup {today} done", flush=True)


def haversine_km(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    """Расстояние по прямой между координатами, км."""
    r = 6371.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp = math.radians(lat2 - lat1)
    dl = math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(math.sqrt(a))


def letter_speed_km_per_min(letter: dict) -> float:
    """Скорость доставки письма, км/мин: базовая 10; если отправитель ИЛИ адресат —
    «быстрый» (сейчас Андрюха) — базовая × множитель; для тестовых пар — 500."""
    if letter.get("chat") == GEO2_CHAT_ID:
        return SANDBOX_FAST_KM_PER_MIN
    mult = LETTER_FAST_SENDERS.get(letter.get("from")) or LETTER_FAST_SENDERS.get(letter["to"])
    if mult:
        return LETTER_SPEED_KM_PER_MIN * mult
    if frozenset((letter["from"], letter["to"])) in LETTER_TEST_PAIRS:
        return LETTER_TEST_SPEED_KM_PER_MIN
    return LETTER_SPEED_KM_PER_MIN


def letter_progress(letter: dict):
    """Текущая позиция письма (по прямой) и флаг прибытия."""
    total = haversine_km(letter["from_lat"], letter["from_lon"], letter["to_lat"], letter["to_lon"])
    elapsed_min = (time.time() - letter["start_ts"]) / 60.0
    done_km = min(elapsed_min * letter_speed_km_per_min(letter), total)
    frac = done_km / total if total > 0 else 1.0
    lat = letter["from_lat"] + (letter["to_lat"] - letter["from_lat"]) * frac
    lon = letter["from_lon"] + (letter["to_lon"] - letter["from_lon"]) * frac
    return lat, lon, total <= 0 or done_km >= total


def letter_sender_name(chat_id: int, letter: dict) -> str:
    """Отображаемое имя отправителя: актуальное имя его метки
    (ник в Telegram мог смениться после отправки); если метка удалена —
    имя, зафиксированное при отправке."""
    m = geo_state.get(chat_id, {}).get(letter["from"])
    return (m or {}).get("name") or letter.get("from_name", "?")


def gift_sender_name(chat_id: int, gift: dict) -> str:
    """Отображаемое имя отправителя подарка: актуальное имя его метки."""
    mkey = resolve_marker_key(chat_id, str(gift.get("from", "")),
                             str(gift.get("from_name", "")))
    m = geo_state.get(chat_id, {}).get(mkey) if mkey else None
    return (m or {}).get("name") or gift.get("from_name", "?")


def duel_display_names(d: dict) -> tuple:
    """Актуальные имена капитанов — с их меток (ник в Telegram мог смениться);
    если метка пропала — имена, зафиксированные при создании боя."""
    def _nm(u, stored):
        m = geo_state.get(d["chat"], {}).get(u)
        return (m or {}).get("name") or stored
    return _nm(d["a"], d["a_name"]), _nm(d["b"], d["b_name"])


# ---------- Ванильный Вулкан Какашек: спавн и полёт какашек ----------

def random_point_near_moscow(radius_km: float):
    """Случайная точка в круге радиусом radius_km от Москвы (равномерно по площади)."""
    r = radius_km * math.sqrt(random.random())  # sqrt — чтобы точки не кучковались у центра
    bearing = random.uniform(0, 2 * math.pi)
    lat1, lon1 = math.radians(MOSCOW_LAT), math.radians(MOSCOW_LON)
    angular = r / 6371.0
    lat2 = math.asin(math.sin(lat1) * math.cos(angular)
                     + math.cos(lat1) * math.sin(angular) * math.cos(bearing))
    lon2 = lon1 + math.atan2(math.sin(bearing) * math.sin(angular) * math.cos(lat1),
                             math.cos(angular) - math.sin(lat1) * math.sin(lat2))
    return math.degrees(lat2), (math.degrees(lon2) + 540) % 360 - 180


def random_point_anywhere():
    """Случайная точка на всей карте (равномерно по широте и долготе)."""
    return random.uniform(-85, 85), random.uniform(-180, 180)


# ---------- Похотливый Кит: маска суши, спавн в океане, полёт подарков ----------
# Битовая маска суши 720×360 (0.5°/пиксель) из Natural Earth 110m, 1 = суша.
LAND_MASK_B64 = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8//8DAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA4P///x8AAAAAAP7/////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADg+P////8fAAAA/P//////fwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPj///////+f/w/4/P//////BwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/////////8////////////z/9/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/Pj//////wf/////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACA//////////////////////////8AAAAAAAAAAAAhAAAAAAD+/wAAAAAAAAAAAAD+DwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADA///9////j////////////////38AAAAAAAAAhP//fwAAAADgDwAAAAAAAAAAAMD/PwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACA////////A+D//////////////w8AAAAAAADw////DwAAAAAAAAAAAAAAAAAAAAD8/wEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA4AEA/P////8fAPD//////////////wcAAAAAAADg//9AAAAAAAAAAAAAAAAAAAAAAAD8/zwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMAf4H988P/+//8D4P///////////////wEAAAAAAADA//8PAAAAAAAAAAAAAAAAAAAAAAAA+P4HAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMAH4P/8wT/////g/////////////////wEAAAAAAAAA/D9+AAAAAAAAAAAAAAAAAAAAAAAAgP8HAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgvAfAAChH4D//x8A/v///////////////wEAAAAAAAAA4B/+AwAAAAAAAAAAAAAAAAAAAAAAQAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACA/4AAAADADwD//xEA/v///////////////wMAAAAAAAAA+AcQAAAAAAAAAAAAAAAAAAAAAAAAAPgfAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADg/wBwAADv//H//x8A+P///////////////w8AAAAAAAAAgAcAAAAAAAAAAAAAAPADAAAAAAAAAPw/fwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8j3/4BPwf/+f/fwAA8P///////////////wEAAAAAAAAAAAAAAAAAAAAAAAAA/P8BAAAAAAD84P///wcAAAAAAOAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgwP/3H/wfxP/BPwAAAAAA/P///////////wEAAAAAAAAAAAAAAAAAAAAAAAD4/wMAAAAAAPD//////x8AAAAAAPj/BwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA8P//H8CP3////wAAAAAA/P///////////wEAAAAAAAAAAAAAAAAAAAAAAID/DwAAAAAAwP///////w8AAAAAAP7/8z8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPAfAADPn////wEAAAAA4P///////////wAAAAAAAAAAAAAAAAAAAAAAAID/AAAAAAAA4P//////fwAAAAAAAOD/gQ8AAAAAAAAAAAAAAAAAAAAAAAAAAMD/H/AAAAAA/IAPEAAAAAAAwP///////////wMAAAAAAAAAAAAAAAAAAAAAAOAfAAAAAAAA8P//////PwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/fwAAPIA//ocfyA8AAAAAgP///////////wAAAAAAAAAAAAAAAAAAAAAAAPgHAAAAAAD+//////////8/wD8AAAAeAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMD//w+A//C//+HH3/8AAAAAAP//////////fwAAAAAAAAAAAAAAAAAAAAAAAPwDAAAIAAD+//////////9/wP8DAID/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAOD/8/8wP/j///D/f/8AAAAAAP7/////////DwAAAAAAAAAAAAAAAAAAAAAAAP8AAAD8YwD+//////////////8DAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPD//f9/P+B/Dvj///8BAAAAAP7/////////CwAAAAAAAAAAAAAAAAAAAAAAwH8AAAD84/j8//////////////8HAMD//w8AAAAAAAAAAwAAAAAAAAAAAAAAAPD//v//f4B/HvD///+PAAAAAP//////////BwAAAAAAAAAAAAAAAAAAAAAAgP8AAAD+8f////////////////8BgZD//x8AAAAAAAAAHwAAAADAAwAAAAAAAAD/8P//fwCOf/D/////AQAAAOT/////////DwAAAAAAAAAAAAAAAgEAAAAAgP8DAOD//f////////////////+P/////38ABAAAAADgBwAAAAD+/xAAAAAAAAAC+P///wCA//D/////fwAAAPj///////+/HwAAAAAAAAAAAAAA/w8AAAAAAPgPAOD/8f//////////////////////////PwAAAADgAAAAAPD///8fAQAAkIMAwP///3+I/8H//////wEAAPz/////////DwAAAAAAAAAAAAD8/38AAAAAAAAAAMD/8////////////////////////////wAAEAAAAAAAAPz/////fwD4/8c+4P///z98/gDw//v//wMAAPz/////////AQAAAAAAAAAAAMD///8BAAAAAAAA/8D/+/////////////////////////////CB8P8AAAAAAP7//////wP/////n////w//+SfwP4D//wcAAGD+//////8/AAAAAAAAAAAAAPj/////AwAAAAAA/uP/+///////////////////////////////4/8/AQAA+P///////////////+P/vw+Y+PfwP8D/fwAAAAD+//////8HAAAAAAAAAAAAAP//////D0AAABgg/D/85///////////////////////////////////HwAA/P///////////////x/A/wP8/v/wH8Dj/w8AAMD///////8BAAAAAAAAAAAAgP//////f4AfAP///////////////////////////////////////////wAAgP////////////////8f///////4P+DD/38AAOD/////fwAAAAAAAAAAAAAA4P///////wE/////////x////////////////////////////////////wcAAP//////////////////////////P8DD//8AAPD/////HwAAAAAAAAAAAAAA8P///////4cP////////8/////////////////////////////////////sBgPn/////////////////////////DwDg//8fAOD/////DwAAAIAAAAAAAAAA+P///////wf+/////////v////////////////////////////////////8H/P/////////////////////////PAwDw//8PAPD/////AwAAD8IHAAAAAAAA/v////8P//H//////////////////////////////////////////////f+f//////////////////////////83AAD4//AHAMD/////AACA//8HAAAAAAAA//8f/P8/EPz/////////////////////////////////////////////i38A/P/////////////////////////zAfD//+MDAID///8BAAAA+P8fAAAAAACA//8H/P8/hP//////////////////////////////////////////////AX8A+P/////////////////////////7B/z//x8BAID//38AAAAA//8PAAAAAADA//8H/v8//v//////////////////////////////////////////////AHAAQPT////////////////////////4X/Dn/z8AAID//38AAAAA8P8HAAAAAADg//+H/////f////////////////////////////////////////////8fAAAPAMj//////////////////////wf+/AAA/z8AAAD//z8AAAAA/B8AAAAAAAD4///w//////////////////////////////////////////////////8fAAB/wP///////////////////////wcQQACA/34AAAD+/z8AAAAAAAQAAAAAAAD+/z/4//////////////////////////////////////////////////8/AAAQwP///////////////////////wcAHiAA/jsAAAD4/wcAAAAAAAAAAAAAAPj//w/8//////////////////////////////////////////////////9/AAAA8P//////////////////////PwAAg/t/wA8AAADw/wcAAAAAAAAAAAAAAPz//w/4/////////////////////////////////////////////3////9AAAAA+P//////////////////////HwAAgPn/AQgAAADg/w8AAAAAAAAAAAAAAP7//wf4/////////////////////////////////////////////7///z8AAAAA4P//////////////////////HwAAAPD/HwAAAADg/wcAAAAAAAAAAAAAAP7//wf4////////////////////////////////////////////g4f//wMAAAAA4P//////////////////////DwAAAPD/HwAAAACA/wMAAAAAAAAAAAAAAPz//w/8////////////////////////////////////////////AOH//wEAAAAA3v//f/7w////////////////BwAAAOD/H0AAAAAAwAMAAAAAAAAAAAAAAPz//z/wH/z///////////////////////////////////////9/APh/OAAAAAAAHP//H/8Awf//////////////BwAAAOD/H+AAAAAAAAAAAAAAAAAAAAAAAPz//x8gCP7///////////////////////////////////////8fAPwTEAAAAAAAAPj/DwcAAPz/////////////BwAAAPD/P/ABAAAAAAAAAAAAAAAAAAAAAPj//x/A/////////////////////////////////////////8N/AH8AAAAAAAAAADD/PwAAAPD/////////////PwAAAPz///gDAAAAAAAAAAAAAAAAAOADAPjH/w/A//////////////////////////////////////8HAMADwD8AAAAAAAAAAADyDwAAAMD/////////////PwAAAOD///8HAAAAAAAAAAAAAAAAAOABAMDB/wMA//////////////////////////////////////8BAAAA8B8AAAAAAAAAAADw8wAAAADw////////////fwAAAMD///8PAAAAAAAAAAAAAAAAAPAfAACg/wEg//////////////////////////////////////8AAAAA/n8AAAAAAAAAAAD8PAAAAADw/////////////wcAAMD///8fAAAAAAAAAAAAAAAAAPAPAAC+/wH4/////////////////////////////////////z8AAAAA/n8AAAAAAAAAAAB+DAAAAADA/////////////z8AAMD///8/AAAAAAAAAAAAAAAAAPgPAAAf/wD8/////////////////////////////////////x8AAACA/38AAAAAAAAAAMAPAAAAAACA//////////////8AAMD///8fAAAAAAAAAAAAAAAAAPAHAAA//wD8/////////////////////////////////////wcAAACA/38AAAAAAAAAAPAPAAAAAAAA//////////////8PAOD/////AAAAAAAAAAAAAAAAAPAPAADvHwD8/////////////////////////////////////wMAAADA/w8AAAAAAAAAAD8AAAAAAAAA////////////////D/j/////AQAAAAAAAAAAAAAAAPcfAADOHwD8/////////////////////////////////////wAAAADA/w8AAAAAAAAAwAMAAAAAAAAA/P//////////////D///////PwAAAAAAAAAAAAAAgN8/AAAOAb///////////////////////////////////////wMAAADA/x8AAAAAAAAAQAAAAAAAAADg/f//////////////D/7/////PwAAAAAAAAAAAAAAwA/+AAD+7////////////////////////////////////////+MwAACA/wEAAAAAAAAAAAAAAAAAAADg4f//////////////D/7//////wAAAAAAAAAAAAAA8A/8AND///////////////////////////////////////////8hAACA/wEAAAAAAAAAAAAAAAAAAADg4P//////////////D/z//////wEAAAAAAAAAAAAA4M//Af7///////////////////////////////////////////8/AACA/wEAAAAAAAAAAAAAAAAAAACA4P//////////////H/z//////wEAAAAAAAAAAAAA4Mf/D/////////////////////////////////////////////9/AACAPwAAAAAAAAAAAAAAAAAAAAAAA///////////////P/z//////wEAAAAAAAAAAAAA4If/D/////////////////////////////////////////////9/AAAAHwAAAAAAAAAAAAAAAAAAAAAAAP//////////////f/7//////wMAAAAAAAAAAAAAcOD/h/////////////////////////////////////////////97AAAAHwAAAAAAAAAAAAAAAAAAAAAAAP7//////////////////////wEAAAAAAAAAAAAAAID/5/////////////////////////////////////////////9zAAAAAgAAAAAAAAAAAAAAAAAAAAAAgP//////////////////////4QAAAAAAAAAAAAAAAMD/+//////////////////////////////////////////////zAAAAAAAAAAAAAAAAAAAAAAAAAAAAgP//////////////////////8AAAAAAAAAAAAAAAAPAB/P/////////////////////////////////////////////zAAAAAAAAAAAAAAAAAAAAAAAAAAAAgP///////////////////8MH8AsAAAAAAAAAAAAAACAQ///////////////////////////////////////////////zAQAAAAAAAAAAAAAAAAAAAAAAAAAAAPD9////////////////fzwf+D8AAAAAAAAAAAAAAADw///////////////////////////////////////////////xAQAAAAAAAAAAAAAAAAAAAAAAAAAAAPD9////////////////P/8A/j8AAAAAAAAAAAAAAMD///////////////////////////////////////////////95AgAAAAAAAAAAAAAAAAAAAAAAAAAAAMD//////////////////z8A/H8AAAAAAAAAAAAAAID///////////////////////////////////////////////8xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAID7/////////////////z8A/n8AAAAAAAAAAAAAAID///////////////////////////////////////////////8wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAID/////////////////9/9AADYAAAAAAAAAAAAAAAD4/////////////////////////////////////////////39wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAID///////////////////9hADsAAAAAAAAAAAAAAADw////////////+////////////////////////////////z/4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD////////////////////vAAAAAAAAAAAAAAAAAADg/////////58/8P///////////////////////////////x+QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/////////////////////AQAAAAAAAAAAAAAAAADg/////////w9++P///////////////////////////////wcYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////////8/AAAAAAAAAAAAAAAAAADg////+f///w///////////////////////////////////wMYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//////////////////+cDAAAAAAAAAAAAAAAAAADg////6f///wd8+P///////////////////////////////wF4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAID///////////////////gAAAAAAAAAAAAAAAAAAADg////w////wMI4P///////////////////////////////wH4BAAAAAAAAAAAAAAAAAAAAAAAAAAAAID/////////////////PzgAAAAAAAAAAAAAAAAAAD/g///wD////wMAwP///////////////////////////////wD8BwAAAAAAAAAAAAAAAAAAAAAAAAAAAID/////////////////BwAAAAAAAAAAAAAAAAAA4P///z/kD/7//wEAgP//////////////////////////////PwD/DwAAAAAAAAAAAAAAAAAAAAAAAAAAAMD/////////////////BwAAAAAAAAAAAAAAAAAAwP//PwDmH/j//wAAAPz///////////////////////////8/DoD/AQAAAAAAAAAAAAAAAAAAAAAAAAAAAID/////////////////DwAAAAAAAAAAAAAAAAAAwP//PwDOP/D//wB4APj///////////////////////////8/AIDnAAAAAAAAAAAAAAAAAAAAAAAAAAAAAID/////////////////HwAAAAAAAAAAAAAAAAAA4P//fwAG/8H//wH/APj///////////////////////////8PAIBHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAID/////////////////BwAAAAAAAAAAAAAAAAAAwP//HwAE/sP/////g/////////////////////////////8PAAAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAID/////////////////AQAAAAAAAAAAAAAAAAAAwP//AwAP8M////z///////////////////////////////8PAIAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAID///////////////8fAAAAAAAAAAAAAAAAAAAAwP//AQAP4N//0f//////////////////////////////8f8HAIAPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////8PAAAAAAAAAAAAAAAAAAAA4P//AAAPgJH/4P///////////////////////////////P8AAAAPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////8HAAAAAAAAAAAAAAAAAAAA4P//AAAPAAd/8P////////////////////////////9/GPwAAAAPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///////////////8HAAAAAAAAAAAAAAAAAAAA8P//AQACgAf+4P////////////////////////////8PBP4BAIAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8//////////////8DAAAAAAAAAAAAAAAAAAAA4P//AAAA/gH88f////////////////////////////8fAP4DAMADAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8//////////////8BAAAAAAAAAAAAAAAAAAAAwP9/AAAA/wH8wf////////////////////////////8/Av4DAOADAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4//////////////8BAAAAAAAAAAAAAAAAAAAAwP8/AHBYeAB4gP//////////////////////////////H+AHAPIDAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4//////////////8BAAAAAAAAAAAAAAAAAAAAwP0P/P9/cAA4gP//////////////////////////////P/AHAP8DAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADw//////////////8BAAAAAAAAAAAAAAAAAAAAAHgA/v8/AABwABie////////////////////////////A+AHAP8DAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADg//////////////8BAAAAAAAAAAAAAAAAAAAAADDg//8/AACAAAAw////////////////////////////AOAH4P8DAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADA//////////////8AAAAAAAAAAAAAAAAAAAAAAPj///8/AACAHwCP//////////////////////////9/AOAH/v8BAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADA//////////////8AAAAAAAAAAAAAAAAAAAAAAPj///8/AAAAAgCf//////////////////////////9/APCB/z8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACA/////////////x8AAAAAAAAAAAAAAAAAAAAAAPz///8fAAAAAACA////////////////////////////AXDg/wMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+P///////////w8AAAAAAAAAAAAAAAAAAAAAAP////8/AAAAAADA////////////////////////////AQDw/wEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA4P///////////wMAAAAAAAAAAAAAAAAAAAAAwP////9/AAAAAADA////////////////////////////AwD8lwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA4P///////////wAAAAAAAAAAAAAAAAAAAAAA4P//////DwA+AADg////////////////////////////AwD4BwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwP//////////fwAAAAAAAAAAAAAAAAAAAAAA4P//////fwD/AADg////////////////////////////BwDwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwP//////////PwAAAAAAAAAAAAAAAAAAAAAA4P//////f4D/HyDw////////////////////////////DwBwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgOf/////////PwAAAAAAAAAAAAAAAAAAAAAA8P///////wP///nz////////////////////////////DwBwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgOf/////////PwAAAAAAAAAAAAAAAAAAAAAA8P///////5//////////////////////////////////DwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMf/////////PwAAAAAAAAAAAAAAAAAAAAAA8P//////////////////////////////////////////DwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAI///////z8gPwAAAAAAAAAAAAAAAAAAAAAA8P//////////////////+///////////////////////HwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAJz/////BzwAfAAAAAAAAAAAAAAAAAAAAAAA+P//////////////////4f//////////////////////DwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAALj/////AQAAfAAAAAAAAAAAAAAAAAAAAAAA/P//////////////////4f//////////////////////DwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHj///9/AAAAfAAAAAAAAAAAAAAAAAAAAADA////////////////////wf//////////////////////DwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP7+//8/AAAAfAAAAAAAAAAAAAAAAAAAAADg//////////////+f////g///////////////////////AwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPj4//8/AAAA/BAAAAAAAAAAAAAAAAAAAADg//////////////+P////B/7/////////////////////AQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPDx//8/AAAA+HwAAAAAAAAAAAAAAAAAAADw//////////////8P////H/z+////////////////////AQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMDh//8/AAAA8CQAAAAAAAAAAAAAAAAAAAD4//////////////8f/v//XyD9////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIDj//8/AAAA8CAAAAAAAAAAAAAAAAAAAAD8//////////////8f/v//34D9////////////////////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAICH//8fAAAA4BgAAAAAAAAAAAAAAAAAAAD8//////////////8//P///8CB//////////////////9/BAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIAH//8fAAAAABgAAAAAAAAAAAAAAAAAAAD+//////////////9//P//f+ABAMD///////////////8/DgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP/v8fAAAAABgAAAAAAAAAAAAAAAAAAAD+//////////////9//P////8DAMD///////////////8PDgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAY/P8fAAAAABAAAAAAAAAAAAAAAAAAAAD/////////////////8P////8/AMD///////////////8HDwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA4+P8fAAAAfAAAAAAAAAAAAAAAAAAAAID/////////////////4P////8/AAD+//////////////8BBwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAY+P8fAACA/wkAAAAAAAAAAAAAAAAAAID/////////////////wf//////AAD8//////////////8ABwAAAAAAAAAAAAAAAAAAAAAAAAADAAAAAAAAAAAAAAAA8P8fAACA+x8AAAAAAAAAAAAAAAAAAMD/////////////////w///////AAD8/////7///////xcAAgAAAAAAAAAAAAAAAAAAAAAAAAAaAAAAAAAAAAAAAAAA8P8fAADCgD8AAAAAAAAAAAAAAAAAAMD/////////////////w/////9/AAD4/////x///////wAAAgAAAAAAAAAAAAAAAAAAAAAAAAB4AAAAAAAAAAAAAAAA4P8/APAHAPgBAAAAAAAAAAAAAAAAAOD/////////////////x/////9/AAD4////PwD///9/OAAAAAAAAAAAAAAAAAAAAAAAAAAAAADAAQAAAAAAAAAAAAAA8P8/APgHAPgHAAAAAAAAAAAAAAAAAOD/////////////////g/////8fAABw/v//fwD///8/GAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwAAAAAAAAAAAAAA8P8/APgDAOAPAAAAAAAAAAAAAAAAAID/////////////////g/////8fAAAA/v//HwD+//8fOAAAAAAAAAAAAAAAAAAAAAAAAAAAAACABwAAAAAAAAAAAAAA4P9/APwBAPDnHwAAAAAAAAAAAAAAAID/////////////////B/7///8PAAAA/v//DwD8//8PfAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABwAAAAAAAAAAAAAAwP//APwDAADAPwAAAAAAAAAAAAAAAID/////////////////B/7///8PAAAA/v//BwD4//8PPgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAAAAAAAAAAAAAAAP//x/8BABC4/w4AAAAAAAAAAAAAAID/////////////////B/z///8PAAAA/v//AQDw//8PHgAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////8BAPj4fx4AAAAAAAAAAAAAAID/////////////////D/j///8DAAAA/P//AADw//8fBAAAHgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPj///8AAPAAAx4AAAAAAAAAAAAAAID/////////////////H/j///8BAAAA/P9/AADg//8/AAAAHwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMD///8AAAAAAAAAAAAAAAAAAAAAAID/////////////////H/D//38AAAAA/P8fAADg//8/AAAAPwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///8AAAAAAAAAAAAAAAAAAAAAAMD/////////////////P+D//y8AAAAA+P8fAADg//9/AAAAHwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4/38IAAAAAAAAAAAAAAAAAAAAAID/////////////////P+D//wEAAAAA+P8PAADw+///AQCAHwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADg8P//AAAAAAAAAAAAAAAAAAAAAMD/////////////////f+D//wEAAAAA+P8DAABg+P//AQCADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwP//AwAAAAAAAAAAAAAAAAAAAMD//////////////////+D/fwAAAAAA8P8BAAAA+P//AwCADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgP//AwAAAAAAAAAAAAAAAAAAAPD//////////////////+H/DwAAAAAA8P8BAAAA+P//AwAADwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//AwAAAAAAAAAAAAAAAAAAAOD//////////////////8f/AwAAAAAA4P8BAAAA8P//AwAAPgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP7/AwAAAAAAAAAAAAAAAAAAAMD//////////////////89/AQAAAAAA4P8BAAAA8P//BwAA/gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOD/AQAAAAAAAAAAAAAAAAAAAMD///////////////////8/AAAAAAAA4P8BAAAA4P//BwAA7wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/AwAAAAAAAAAAAAAAAAAAAMD///////////////////8HAAAAAAAA4P8AAAAA4P//BwAABgcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD+AwAAEwAAAAAAAAAAAAAAAMD//////////////////38AYAAAAAAAwP8AAAAA8OH/BwAABA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8AQDAGwAAAAAAAAAAAAAAAID//////////////////38AeAAAAAAAwP8AAAAA4MD/BwAAeA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4AQD8eQAAAAAAAAAAAAAAAAD//////////////////3+AfwAAAAAAgP8AAAAA4MD/AQCAcA8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADwAQD+/49/AAAAAAAAAAAAAAD8///////////////////4fwAAAAAAAP8AAAAAcMD/AADA+AcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADwAwD+//93AAAAAAAAAAAAAAD8////////////////////PwAAAAAAAP8AAAAAYAB/AABg8AYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADwBwP//v8fAAAAAAAAAAAAAAD4////////////////////PwAAAAAAAD8BAAAAYAAcAAAw8AQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACA34////9/AAAAAAAAAAAAAADw////////////////////PwAAAAAAAH4DAAAA4AAOAAA4YBwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////////AAAAAAAAAAAAAADg////////////////////HwAAAAAAAJ4HAAAA8AAEAAAIQB4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//j/////AQAAAAAAAAAAAADg////////////////////HwAAAAAAAIwHAAAA8AEAAAAE8B8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA8Pj/////AwAAAAAAAAAAAADA////////////////////DwAAAAAAAIgPAAAA8AEAAAAA8B8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwPD/////DwAAAAAAAAAAAACA////////////////////DwAAAAAAAIAPAAAAgAEAAAAAeD8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOD/////DwAAAAAAAAAAAAAA////////////////////BwAAAAAAAIAPAAAAgA8AAAAGkBcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOD/////HwIAAAAAAAAAAAAA/P//////////////////BwAAAAAAAAAPAAAAAB8AAAAPAB8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPD//////x8AAAAAAAAAAAAA8P//B/z/////////////AwAAAAAAAAABAAAAAD8AAIAfAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOD//////38AAAAAAAAAAAAA4P9/APz/////////////AwAAAAAAAAAAAADABz8AAMB/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOD///////8BAAAAAAAAAAAA4B8eAPz/////////////AQAAAAAAAAAAAADAD34AAPAfAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOD///////8DAAAAAAAAAAAAAAEAAHj/////////////AAAAAAAAAAAAAACAH34AAPA/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOD///////8DAAAAAAAAAAAAAAAAAAD+//////////9/AAAAAAAAAAAAAAAAf34AAPgHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPD///////8DAAAAAAAAAAAAAAAAAAD4//////////9/AAAAAAAAAAAAAAAA/HwAAP4HAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPj///////8DAAAAAAAAAAAAAAAAAAD4//////////8/AAAAAAAAAAAAAAAA+P0AwP8PAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPz///////8HAAAAAAAAAAAAAAAAAAD4//////////8PAAAAAAAAAAAAAAAA+P8AyP8fAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPz///////8fAAAAAAAAAAAAAAAAAAD4//////////8DAAAAAAAAAAAAAAAA4O8B+P8PAIQDAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPz///////8fAAAAAAAAAAAAAAAAAAD8//////////8BAAAAAAAAAAAAAAAA4J8B/P8fDsYDAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgP////////8PAAAAAAAAAAAAAAAAAAD8//////////8AAAAAAAAAAAAAAAAAwH8A/P8//8MDAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgP////////8HAAAAAAAAAAAAAAAAAAD8/////////38AAAAAAAAAAAAAAAAAwP8A/v+H/4EDAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgP////////9/AAAAAAAAAAAAAAAAAAD8/////////z8AAAAAAAAAAAAAAAAAgH8A/P+HAYAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwP////////9/BwAAAAAAAAAAAAAAAAD+/////////x8AAAAAAAAAAAAAAAAAAH8A+P/PfQDhDwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwP//////////HwAAAAAAAAAAAAAAAAD+/////////w8AAAAAAAAAAAAAAAAAAP8B+P/DXwDgHwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwP//////////fwAAAAAAAAAAAAAAAAD8/////////w8AAAAAAAAAAAAAAAAAAP4D8P/DHwCAHxwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwP///////////wIAAAAAAAAAAAAAAAD8/////////wMAAAAAAAAAAAAAAAAAAP4P8P/DDwAAH/8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgP////////////8BAAAAAAAAAAAAAADw/////////wEAAAAAAAAAAAAAAAAAAPwP8P/jHwCHn/8HAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgP////////////8DAAAAAAAAAAAAAADg/////////wEAAAAAAAAAAAAAAAAAAPgfQP/BH/gf/v8/AMABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwP////////////8HAAAAAAAAAAAAAADA/////////wAAAAAAAAAAAAAAAAAAAPAPAOCBHzAg/v//AwAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA4P////////////8PAAAAAAAAAAAAAADA/////////wAAAAAAAAAAAAAAAAAAAOAPACCBOQAAxv//B4AHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA4P////////////8/AAAAAAAAAAAAAACA////////fwAAAAAAAAAAAAAAAAAAAMAPAACAbQAAgP//D4ADAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwP//////////////AwAAAAAAAAAAAACA////////PwAAAAAAAAAAAAAAAAAAAIAPAADAcQAAEPj/D/kgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwP//////////////AwAAAAAAAAAAAAAA////////PwAAAAAAAAAAAAAAAAAAAAB+AACAIQAAMPD/P39gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA4P//////////////BwAAAAAAAAAAAAAA////////PwAAAAAAAAAAAAAAAAAAAAD4IQAAAAAAMPD//z7AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwP//////////////BwAAAAAAAAAAAAAA/v//////fwAAAAAAAAAAAAAAAAAAAAD8/wMAAAAAEOD//wDAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP//////////////BwAAAAAAAAAAAAAA/v//////fwAAAAAAAAAAAAAAAAAAAADw/wMAAAAAAOD/fwAAHgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP7/////////////BwAAAAAAAAAAAAAA/v//////fwAAAAAAAAAAAAAAAAAAAAAA/x8AAAAAAPD//wAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP7/////////////AwAAAAAAAAAAAAAA/P//////fwAAAAAAAAAAAAAAAAAAAAAA4P+8M3gAAPh/8AEAwAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPz/////////////AwAAAAAAAAAAAAAA/v//////fwAAAAAAAAAAAAAAAAAAAAAAACD8Pz4AAAB+4AEAgAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPz/////////////AQAAAAAAAAAAAAAA/v///////wAAAAAAAAAAAAAAAAAAAAAAAACGgA8AAAA8wAcAgAUAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPj/////////////AQAAAAAAAAAAAAAA/P///////wAAAAAAAAAAAAAAAAAAAAAAAADggwMAAAAAgB8AgAsAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPj/////////////AAAAAAAAAAAAAAAA/P///////wEAAAAAAAAAAAAAAAAAAAAAAAAAwwEAAAAAgD8AABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPD///////////9/AAAAAAAAAAAAAAAA+P///////wEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgADAAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPD///////////8/AAAAAAAAAAAAAAAA+P///////wEAAAAAAAAAAAAAAAAAAAAAAAAAAACABwAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOD///////////8fAAAAAAAAAAAAAAAA+P///////wEAAAAAAAAAAAAAAAAAAAAAAAAAAAAArgF4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOD///////////8fAAAAAAAAAAAAAAAA/P///////wEADgAAAAAAAAAAAAAAAAAAAAAAAADA/wN4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMD///////////8PAAAAAAAAAAAAAAAA/P///////wMADgAAAAAAAAAAAAAAAAAAAAAAAADg/wP4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMD///////////8PAAAAAAAAAAAAAAAA/v///////wMADgAAAAAAAAAAAAAAAAAAAAAAAADw/wH4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAID///////////8HAAAAAAAAAAAAAAAA/v///////wOAHwAAAAAAAAAAAAAAAAAAAAAAAGD4/wH4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAID///////////8HAAAAAAAAAAAAAAAA/////////wMAHwAAAAAAAAAAAAAAAAAAAAAAAPj8/wD4AgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAID///////////8HAAAAAAAAAAAAAAAA/////////wOAHwAAAAAAAAAAAAAAAAAAAAAAAPz//wD4BwAAAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD+//////////8HAAAAAAAAAAAAAAAA/////////wHgHwAAAAAAAAAAAAAAAAAAAAAAAP7//wD4BwAAAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4//////////8HAAAAAAAAAAAAAACA/////////wH4HwAAAAAAAAAAAAAAAAAAAAAAAP///wf8BwAAAABgAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADg//////////8HAAAAAAAAAAAAAACA/////////wH/HwAAAAAAAAAAAAAAAAAAAAAAwP///w/8BwAAAADAAADAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACA//////////8DAAAAAAAAAAAAAACA////////fwD/DwAAAAAAAAAAAAAAAAAAAAAA4P///z/8DwAAAACAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/v////////8DAAAAAAAAAAAAAACA////////P4D/BwAAAAAAAAAAAAAAAAAAAAAA8P///3/+DwAAAAAAAAA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/v////////8DAAAAAAAAAAAAAACA////////BwD/BwAAAAAAAAAAAAAAAAAAAAAA8P//////HwAAAAAAAAA8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+P////////8BAAAAAAAAAAAAAACA////////AwD/BwAAAAAAAAAAAAAAAAAAAAAA8P//////HwAAAAAAAAA8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+P////////8BAAAAAAAAAAAAAAAA////////AQD/BwAAAAAAAAAAAAAAAAAAAAAA+P//////HwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+P////////8BAAAAAAAAAAAAAAAA/v////9/AAD/BwAAAAAAAAAAAAAAAAAAAAAA/P//////fwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+P////////8BAAAAAAAAAAAAAAAA/v////9/AAD/AwAAAAAAAAAAAAAAAAAAAADA/////////wEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+P////////8AAAAAAAAAAAAAAAAA/P////8/AAD/AwAAAAAAAAAAAAAAAAAAAADw/////////wMAAAAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+P///////38AAAAAAAAAAAAAAAAA/P////8/AID/AQAAAAAAAAAAAAAAAAAAAAD+/////////wMAAAAGAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+P///////38AAAAAAAAAAAAAAAAA+P////9/AMD/AQAAAAAAAAAAAAAAAAAAAMD//////////wcAAAAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+P///////38AAAAAAAAAAAAAAAAA+P////9/AMD/AAAAAAAAAAAAAAAAAAAAAPD//////////wcAAAA8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+P///////x8AAAAAAAAAAAAAAAAA8P//////AMD/AAAAAAAAAAAAAAAAAAAAAPj//////////z8AAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+P///////x8AAAAAAAAAAAAAAAAA8P//////AMD/AAAAAAAAAAAAAAAAAAAAAPj//////////z8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+P//////fwAAAAAAAAAAAAAAAAAA8P//////AID/AAAAAAAAAAAAAAAAAAAAAPj//////////z8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+P//////PwAAAAAAAAAAAAAAAAAA8P//////AID/AAAAAAAAAAAAAAAAAAAAAPj//////////38AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+P//////DwAAAAAAAAAAAAAAAAAA8P////9/AIB/AAAAAAAAAAAAAAAAAAAAAPz///////////8BAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+P//////AQAAAAAAAAAAAAAAAAAA4P////8fAAB/AAAAAAAAAAAAAAAAAAAAAPj///////////8BAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/P//////AAAAAAAAAAAAAAAAAAAA4P////8HAAAeAAAAAAAAAAAAAAAAAAAAAPD///////////8DAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/P//////AAAAAAAAAAAAAAAAAAAA4P////8DAAAEAAAAAAAAAAAAAAAAAAAAAPz///////////8DAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/P////9/AAAAAAAAAAAAAAAAAAAA4P////8DAAAAAAAAAAAAAAAAAAAAAAAAAPz///////////8HAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/P////9/AAAAAAAAAAAAAAAAAAAAwP////8DAAAAAAAAAAAAAAAAAAAAAAAAAPz///////////8HAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/P//////AAAAAAAAAAAAAAAAAAAAwP////8DAAAAAAAAAAAAAAAAAAAAAAAAAPD///////////8HAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/P////9/AAAAAAAAAAAAAAAAAAAAgP////8BAAAAAAAAAAAAAAAAAAAAAAAAAPD///////////8HAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/P////9/AAAAAAAAAAAAAAAAAAAAAP////8BAAAAAAAAAAAAAAAAAAAAAAAAAPD///////////8PAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/v////9/AAAAAAAAAAAAAAAAAAAAAP////8BAAAAAAAAAAAAAAAAAAAAAAAAAOD///////////8PAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/v////8fAAAAAAAAAAAAAAAAAAAAAP7///8AAAAAAAAAAAAAAAAAAAAAAAAAAMD///////////8HAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/v////8PAAAAAAAAAAAAAAAAAAAAAPz//z8AAAAAAAAAAAAAAAAAAAAAAAAAAMD///////////8HAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/v////8PAAAAAAAAAAAAAAAAAAAAAPj//z8AAAAAAAAAAAAAAAAAAAAAAAAAAOD///////////8HAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////8HAAAAAAAAAAAAAAAAAAAAAPj//x8AAAAAAAAAAAAAAAAAAAAAAAAAAMD///////////8HAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////8DAAAAAAAAAAAAAAAAAAAAAPD//x8AAAAAAAAAAAAAAAAAAAAAAAAAAID///////////8DAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/v////8BAAAAAAAAAAAAAAAAAAAAAPD//wcAAAAAAAAAAAAAAAAAAAAAAAAAAID///8P//////8DAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/v////8AAAAAAAAAAAAAAAAAAAAAAPD//wMAAAAAAAAAAAAAAAAAAAAAAAAAAID//38A/v////8BAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/v///38AAAAAAAAAAAAAAAAAAAAAAPj//wEAAAAAAAAAAAAAAAAAAAAAAAAAAID//wcA8P////8BAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////38AAAAAAAAAAAAAAAAAAAAAAPD/fwAAAAAAAAAAAAAAAAAAAAAAAAAAAID//wEA4P////8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////z8AAAAAAAAAAAAAAAAAAAAAAPD/HwAAAAAAAAAAAAAAAAAAAAAAAAAAAMD//wAAwPv//38AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/////x8AAAAAAAAAAAAAAAAAAAAAAPAPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMB/EAAAwPn//38AAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACA////nwcAAAAAAAAAAAAAAAAAAAAAAIABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/AAAAgPz//z8AAAAAAAYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACA////PwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAeAAAAAP7//z8AAAAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADA////PwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPD//x8AAAAAABgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADA////fwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAID//x8AAAAAADgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADg////fwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAID//w8AAAAAAPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADw////PwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAID//w8AAAAAAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADw////PwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//wcAAAAAAOA/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADw////HwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD+fwAAAAAAAOAfAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADg////AwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADgPAAAAAAAAOAfAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADg//8PAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEAAAAAAAAPgPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADw//8PAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPgHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADw//8PAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMIDAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADw//8PAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAhgEAAAAAAM8DAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4/z8HAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/gEAAAAAAP8BAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4/z8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/AEAAAAAgF8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4//8BAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/AEAAAAAgA8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADY//8DAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/AAAAAAAwAcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADY/z8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+AAAAAAA4AMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADg/z8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMAAAAAAA/gcAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4/z8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4/z8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACAfwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8/x8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADAPwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8/wMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADgPwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD+/wEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADgDwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//wMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8/x8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD+/x8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD+/x8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//wMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD//wEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD+/wEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAeAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD+fwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8PwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8PwAABQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD+fwDgHwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8/wBAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8fwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADw+wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADg/wEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACA/w8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/z8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/jsAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADgBwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOAHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPgBAAAAAAAAAAAAAOABAAgAAAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPgPAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgP8HAAAAAAAAgAEAAPgDwD8AQADg/wEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP4BAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA4P8HAAAAAAAAwAMAAP////8H+P//////BwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////AAEAAADw////////////////////HwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4////x/8DAAD+////////////////////PwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOD///////8HAMD//////////////////////wMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACP8BAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA8AP7///////8PAPD///////////////////////9/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAnv8DAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD+B/////////8PAPj/////////////////////////HwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//8HAAAAAAAAAAAAAAAAAAAAAIAABHwAAPD///////////8P+P///////////////////////////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAv/8PAAAAAAAAAAAAAAAAAAAAAPAf//8P/v////////////8A/P///////////////////////////wMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA//8fAAAAAAAAAAAAAAAAAAQAwP////////////////////8H/P//////////////////////////////AQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADw//8fAAAAAAAAAAAAAAAAOP5//v////////////////////+D////////////////////////////////PwAAAAAAAAAAAAAAAAAAAAAAAAAAAPhHAAAAAAD+f/4fAAAAAAAAAAAAAAAA/v////////////////////////+A////////////////////////////////fwAAAAAAAAAAAAAAAAAAAAAAAAAAAPB/AAAAAAD8f/4/AAAAAAAAAAAAAACA////////////////////////////////////////////////////////////fwAAAAAAAAAAAAAAAAAAAAAAAAAAAP+DACAAAAAAAv8/AAAAAAAAAAAAAAD4////////////////////////////////////////////////////////////HwAAAAAAAAAAAAAAAAAAAB4IBAAAAP4P/v8/wBDA//9/AAAAAAAAAAAAAID/////////////////////////////////////////////////////////////DwAAAAAAAAAAAAAAAAAAAPD8AxAAAP7///////////9/AAAAAAAAAAAAAID/////////////////////////////////////////////////////////////BwAAAAAAAAAAAAAAAAD+/4f3/38CAPz///////////8/AAAAAAAAAAAAAAD///////////////////////////////////////////////////////////9/AAAAAAAAAAAAAAAAAPz///////9/wMP///////////8DAAAAAAAAAAAAAMD///////////////////////////////////////////////////////////8PAAAAAAAAAAAAAAB4/P////////////////////////8AAAAAAAAAAAAAAPz///////////////////////////////////////////////////////////8DAAAAAAAAAAAAAAD4/////////////////////////x8AAAAAAAAAAAAA4P////////////////////////////////////////////////////////////8AAAAAAAAAAAAAAAD4/////////////////////////wAAAAAAAAAAAAD///////////////////////////////////////////////////////////////8AAAAAAAAAAAAYAMD/////////////////////////BwAAAAAAAAAAAMD//////////////////////////////////////////////////////////////38AAAAAAAAAAAD4//////////////////////////8DAAAAAAAAAAAAAPz///////////////////////////////////////////////////////////////8BAAAAAAAAAAD4//////////////////////////8fAAAAAAAABAAA8P////////////////////////////////////////////////////////////////8BAAAAAAAAAD74//////////////////////////8HAAAAAADg/wEA//////////////////////////////////////////////////////////////////8/AAAAAAAAAP8A/////////////////////////x8AAAAAAADw/wEA//////////////////////////////////////////////////////////////////8/AAAAAAAAAPgD/v///////////////////////w8AAAAAAAD4/wMA//////////////////////////////////////////////////////////////////8AAAAAAAAAACAAAID//////////////////////38AAABgAAD//wMAAPD//////////////////////////////////////////////////////////////wMAAAAAAAAAAAAAAAD4//////////////////////8/APj/AfD//wMAAMD//////////////////////////////////////////////////////////////wMAAAAAAAAAAAAAAAD+////////////////////////A/D/Afj/BwAA+P///////////////////////////////////////////////////////////////wEAAAAAAAAAAADA/////////////////////////////x+AAAAIAMD//////////////////////////////////////////////////////////////////wcAAAAAAAAAAAAA/P////////////////////////////8DAADwf/j//////////////////////////////////////////////////////////////////w8AAAAAAAAAAAAAwP//////////////////////////////AfD///////////////////////////////////////////////////////////////////////8AAAAAAAAAAAAA4P//////////////////////////////5/////////////////////////////////////////////////////////////////////////8HAAAAAAAAAAAA4P//////////////////////////////////////////////////////////////////////////////////////////////////////////AwAAAAAQAAAA8P//////////////////////////////////////////////////////////////////////////////////////////////////////////BwAA/uF/AAAAAPj///////////////////////////////////////////////////////////////////////////////////////////////////////////8f/////wAAAAD8/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////wfw////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////"
_LAND_MASK = None


def is_water(lat: float, lon: float) -> bool:
    """True, если точка в океане по встроенной маске суши."""
    global _LAND_MASK
    if _LAND_MASK is None:
        _LAND_MASK = base64.b64decode(LAND_MASK_B64)
    W, H = 720, 360
    if not (-90 <= lat <= 90 and -180 <= lon < 180):
        return False
    x = min(int((lon + 180.0) / 360.0 * W), W - 1)
    y = min(max(int((90.0 - lat) / 180.0 * H), 0), H - 1)
    i = y * W + x
    return not ((_LAND_MASK[i >> 3] >> (i & 7)) & 1)


# Моря, где может появиться кит: (центр_lat, центр_lon, радиус_км)
SEA_REGIONS = [
    (35.0, 20.0, 1200),     # Средиземное
    (43.5, 34.0, 450),      # Чёрное
    (46.0, 36.0, 150),      # Азовское
    (58.5, 20.0, 550),      # Балтийское
    (73.0, 35.0, 600),      # Баренцево
    (68.0, 8.0, 500),       # Норвежское
    (76.0, 5.0, 700),       # Северное
    (75.0, 75.0, 600),      # Карское
    (55.0, 150.0, 700),     # Охотское
    (38.0, 137.0, 600),     # Японское
    (35.0, 123.0, 500),     # Жёлтое
    (62.0, -175.0, 600),    # Берингово
    (15.0, 65.0, 1000),     # Аравийское
    (22.0, 38.0, 600),      # Красное
    (-18.0, 152.0, 700),    # Коралловое
]


def random_point_in_circle(lat0: float, lon0: float, radius_km: float):
    """Случайная точка в круге radius_km вокруг (lat0, lon0), равномерно по площади."""
    r = radius_km * math.sqrt(random.random())
    bearing = random.uniform(0, 2 * math.pi)
    lat1, lon1 = math.radians(lat0), math.radians(lon0)
    angular = r / 6371.0
    lat2 = math.asin(math.sin(lat1) * math.cos(angular)
                     + math.cos(lat1) * math.sin(angular) * math.cos(bearing))
    lon2 = lon1 + math.atan2(math.sin(bearing) * math.sin(angular) * math.cos(lat1),
                             math.cos(angular) - math.sin(lat1) * math.sin(lat2))
    return math.degrees(lat2), (math.degrees(lon2) + 540) % 360 - 180


def random_ocean_point():
    """Случайная точка в воде: в половине случаев — в одном из морей, иначе в любом океане.
    Суша отбраковывается по маске, поэтому точка всегда окажется в реальной воде."""
    for _ in range(300):
        if random.random() < 0.5:
            clat, clon, r = random.choice(SEA_REGIONS)
            lat, lon = random_point_in_circle(clat, clon, r)
        else:
            lat = random.uniform(-75, 75)
            lon = random.uniform(-180, 180)
        if is_water(lat, lon):
            return lat, lon
    return -30.0, -140.0  # запасной вариант — Тихий океан


def submarine_get_active(chat_id: int):
    """Активная подводная лодка чата и флаг «только что заспавнилась».
    Спавн — как у вулкана: час + случайные 0–50 минут после прежнего спавна.
    Уведомление в чат о появлении НЕ отправляется."""
    now = time.time()
    s = submarine_state.get(chat_id)
    if s is not None and now - s["spawn_ts"] < SUBMARINE_LIFETIME_SEC:
        return s, False
    next_spawn = s.get("next_spawn", 0.0) if s else 0.0
    if now >= next_spawn:
        lat, lon = random_ocean_point()
        s = {"lat": lat, "lon": lon, "spawn_ts": now, "used": False,
             "next_spawn": now + SUBMARINE_PERIOD_SEC + random.uniform(0, 3000)}
        submarine_state[chat_id] = s
        submarine_save_to_github()
        print(f"[paint_bot] 🐳 кит для чата {chat_id}: {lat:.2f}, {lon:.2f}", flush=True)
        return s, True
    return None, False


async def submarine_spawn_job(context) -> None:
    """Фоновая проверка раз в минуту: спавн лодок БЕЗ уведомления в чат."""
    for chat_id in ALLOWED_GROUPS:
        with geo_lock:
            _, spawned = submarine_get_active(chat_id)
        if spawned:
            logline(f"submarine spawned chat={chat_id} (без уведомления в чат)")


def gift_speed_km_per_min(gift: dict) -> float:
    """Скорость подарка: 500 км за 10 минут; адресат из LETTER_FAST_SENDERS — ещё быстрее."""
    if gift.get("chat") == GEO2_CHAT_ID:
        return SANDBOX_FAST_KM_PER_MIN
    mult = LETTER_FAST_SENDERS.get(gift["to"])
    return GIFT_SPEED_KM_PER_MIN * mult if mult else GIFT_SPEED_KM_PER_MIN


def gift_progress(gift: dict):
    """Текущая позиция подарка (по прямой) и флаг прибытия."""
    total = haversine_km(gift["from_lat"], gift["from_lon"], gift["to_lat"], gift["to_lon"])
    elapsed_min = (time.time() - gift["start_ts"]) / 60.0
    done_km = min(elapsed_min * gift_speed_km_per_min(gift), total)
    frac = done_km / total if total > 0 else 1.0
    lat = gift["from_lat"] + (gift["to_lat"] - gift["from_lat"]) * frac
    lon = gift["from_lon"] + (gift["to_lon"] - gift["from_lon"]) * frac
    return lat, lon, total <= 0 or done_km >= total


VOLCANO_NOTIFY_TEXT = ("🌋 Ванильный Какашечный Вулкан готов к Извержению! "
                       "Он появился на карте чата на 5 минут — успей нажать на него и "
                       "направить Розовую Какашку 💩🩷 в любого участника. "
                       "Кто первый изверг, тот и молодец 🙂")


def volcano_get_active(chat_id: int):
    """Активный вулкан чата и флаг «только что заспавнился».
    Спавн идёт по расписанию: после каждого спавна next_spawn ставится на
    час + случайные 0–50 минут — момент появления каждый раз разный."""
    now = time.time()
    v = volcano_state.get(chat_id)
    if v is not None and now - v["spawn_ts"] < VOLCANO_LIFETIME_SEC:
        return v, False
    next_spawn = v.get("next_spawn", 0.0) if v else 0.0
    if now >= next_spawn:
        lat, lon = random_point_near_moscow(VOLCANO_RADIUS_KM)
        v = {"lat": lat, "lon": lon, "spawn_ts": now, "used": False,
             "next_spawn": now + VOLCANO_PERIOD_SEC + random.uniform(0, 3000)}
        volcano_state[chat_id] = v
        volcano_save_to_github()
        print(f"[paint_bot] 🌋 вулкан для чата {chat_id}: {lat:.2f}, {lon:.2f}", flush=True)
        return v, True
    return None, False  # перерыв между спавнами ещё не закончился


async def delete_event_message(context) -> None:
    """Удалить уведомление о событии (вулкан/метеорит) после окончания его жизни."""
    chat_id, msg_id = context.job.data
    try:
        await context.bot.delete_message(chat_id, msg_id)
    except Exception as e:
        print(f"[paint_bot] не смог удалить уведомление о событии {chat_id}/{msg_id}: {e!r}", flush=True)


def schedule_event_cleanup(context, chat_id: int, msg_id: int, lifetime_sec: int) -> None:
    """Через lifetime_sec уведомление о событии уже неактуально — удаляем его из чата."""
    context.job_queue.run_once(delete_event_message, when=lifetime_sec, data=(chat_id, msg_id))


BC_CLEANUP_DELAY_SEC = 300  # ответы бота в «Быках и коровах» удаляются через 5 минут после конца игры


def schedule_bc_cleanup(context, chat_id: int, msg_ids) -> None:
    """Автоудаление ответов бота по игре «Быки и коровы» через 5 минут после её конца."""
    for mid in msg_ids:
        context.job_queue.run_once(delete_event_message, BC_CLEANUP_DELAY_SEC, data=(chat_id, mid))


def collect_bc_msg_ids(chat_id: int, user_id: int, kind: str):
    """Id сообщений бота с ответами игры — до завершения активности (solo/duel)."""
    if kind == "solo":
        game = solo_games.get((chat_id, user_id))
        return list(game.get("msg_ids", [])) if game else []
    if kind == "duel":
        duel = duels.get(chat_id)
        return list(duel.get("msg_ids", [])) if duel else []
    return []


async def volcano_spawn_job(context) -> None:
    """Фоновая проверка раз в минуту: спавн вулканов и уведомление в чат."""
    for chat_id in ALLOWED_GROUPS:
        with geo_lock:
            v, spawned = volcano_get_active(chat_id)
        if not spawned:
            continue
        try:
            msg = await context.bot.send_message(chat_id, VOLCANO_NOTIFY_TEXT)
            # событие живёт 5 минут — после этого уведомление уже неактуально, удаляем
            schedule_event_cleanup(context, chat_id, msg.message_id, VOLCANO_LIFETIME_SEC)
            logline(f"volcano spawned chat={chat_id} lat={v['lat']:.2f} lon={v['lon']:.2f} +notify")
        except Exception as e:
            logline(f"volcano spawned chat={chat_id}, но уведомление не ушло: {e!r}")


SAGA_NAG_PHRASES = [
    "📜😢 Пергамент плачет, перышко дрожит… 8 часов никто не продолжает Сагу! "
    "История замирает на самом интересном месте. Не бросайте её в беде — "
    "напишите главу сообщением «saga <твоя глава>» прямо в чат (30–280 символов) 🥺📖",
    "📜🥀 Сага скучает по вам… Уже 8 часов ни одной новой главы. Где ваше воображение, "
    "капитаны перьев? Продолжение — сообщением «saga <твоя глава>» в чат (30–280 символов) ✍️",
    "📜🌙 Ночная смена дозорных закончилась, а главы всё нет… 8 часов молчания! "
    "Спасите Сагу от вечного сна — «saga <твоя глава>» в чат (30–280 символов) 🙏",
]


async def saga_nag_job(context) -> None:
    """Раз в 30 минут: если сага активна и 8ч никто не писал главу — слезливое
    напоминание в чат (не чаще раза в 8 часов; сага не начата — молчим)."""
    now = time.time()
    for chat_id, s in list(saga_state.items()):
        last = float(s.get("last_chapter_ts") or s.get("started_ts") or now)
        if now - last < SAGA_NAG_SEC:
            continue
        if now - float(s.get("last_nag_ts") or 0) < SAGA_NAG_SEC:
            continue
        s["last_nag_ts"] = now
        saga_save_to_github()
        try:
            msg = await context.bot.send_message(
                chat_id, random.choice(SAGA_NAG_PHRASES))
            schedule_event_cleanup(context, chat_id, msg.message_id, 600)
            logline(f"saga nag chat={chat_id} chapters={len(s.get('chapters', []))} +notify")
        except Exception as e:
            logline(f"saga nag chat={chat_id}, но уведомление не ушло: {e!r}")


SIFA_ROTATE_PHRASES = [
    "🐬📢 Официально океана: Сифа теперь у {name}. Остальные — притворитесь брёвнышками 🪵",
    "🐬♻️ Ротация! Сифа переплыла к {name}. Прежний владелец выдохся (или съеден) 🦈",
    "🐬 Внимание, вода в кабине: Сифа числится теперь за {name}. Молитесь, касатки 🙏",
    "🐬 Смена титула! Сифа теперь «{name}». Старая касатка передала эстафету и уплыла в закат 🌅",
    "🐬😱 Тревога: Сифа обосновалась у {name}. Всем всплыть и сделать вид, что вы — остров 🏝️",
]

SIFA_STALE_PHRASES = [
    "🐬😢 Прошло уже 8 часов, а Сифа всё у {name}… Никто её не догоняет, никто не отбирает. "
    "Касатка скучает по погоням! Кто хочет забрать титул — плывите и перехватывайте эстафету 🏁",
    "🐬🥀 8 часов Сифа не меняет хозяина — {name} держится за титул мёртвой хваткой! "
    "Неужели в океане не нашлось смельчака, который догонит касатку? 🏊",
    "🐬⏰ Восьмичасовое молчание океана: Сифа по-прежнему у {name}. Даже брёвнышки уже "
    "смеются. Касатки, вперёд — титул сам себя не перехватит! 🏁",
]


def _sifa_note_holder(entry: dict, ships: dict, now: float) -> None:
    """Запомнить держателя Сифы и момент смены (для напоминаний о застое)."""
    holder = next((u for u, s in ships.items() if s.get("sifa")), None)
    if holder is None:
        return
    if entry.get("sifa_holder") != holder:
        entry["sifa_holder"] = holder
        entry["sifa_since"] = now


def _sifa_grant(entry: dict, ships: dict, user: str) -> None:
    """Дать Сифу касатке и зафиксировать факт владения (для статистики недели)."""
    ships[user]["sifa"] = True
    holds = entry.setdefault("sifa_holds", {})
    holds[user] = holds.get(user, 0) + 1


async def sifa_sweep_job(context) -> None:
    """Раз в 10 минут: касатки игроков, не заходивших 48ч, удаляются (молча —
    новая создастся при входе); раз в 8ч Сифа случайно переходит к другой
    живой касатке, в чат уходит шутливое уведомление; если держатель Сифы не
    менялся 8ч — слезливое напоминание (не чаще раза в 8ч)."""
    now = time.time()
    for chat_id in list(sifa_state.keys()):
        rotate_name = None
        nag_name = None
        with sifa_lock:
            entry = _sifa_entry(chat_id)
            ships = entry["ships"]
            stale = [u for u, s in ships.items()
                     if now - float(s.get("ts", 0) or 0) > SIFA_ABSENT_SEC]
            for u in stale:
                del ships[u]
            if ships and not any(s.get("sifa") for s in ships.values()):
                _sifa_grant(entry, ships, random.choice(list(ships)))
            if ships and now >= entry.get("next_sifa_rotate_ts", 0):
                for s in ships.values():
                    s["sifa"] = False
                holder_u = random.choice(list(ships))
                _sifa_grant(entry, ships, holder_u)
                entry["next_sifa_rotate_ts"] = now + SIFA_ROTATE_SEC
                rotate_name = ships[holder_u].get("name", "капитан")
            if ships:
                _sifa_note_holder(entry, ships, now)
                # ротация каждые 8ч сама сбрасывает таймер: до напоминания
                # дойдёт только если держатель остался тем же (или передача
                # по догону давно — смена держателя сбрасывает sifa_since)
                since = float(entry.get("sifa_since") or now)
                if (now - since >= SIFA_ROTATE_SEC
                        and now >= entry.get("next_sifa_nag_ts", 0)):
                    entry["next_sifa_nag_ts"] = now + SIFA_ROTATE_SEC
                    nag_name = (ships.get(entry["sifa_holder"]) or {}).get(
                        "name", "капитан")
            if stale or rotate_name or nag_name:
                sifa_save_to_github()
        if rotate_name:
            try:
                msg = await context.bot.send_message(
                    chat_id, random.choice(SIFA_ROTATE_PHRASES).format(name=rotate_name))
                schedule_event_cleanup(context, chat_id, msg.message_id, 600)
                logline(f"sifa rotated chat={chat_id} -> {rotate_name!r} +notify")
            except Exception as e:
                logline(f"sifa rotated chat={chat_id}, но уведомление не ушло: {e!r}")
        if nag_name:
            try:
                msg = await context.bot.send_message(
                    chat_id, random.choice(SIFA_STALE_PHRASES).format(name=nag_name))
                schedule_event_cleanup(context, chat_id, msg.message_id, 600)
                logline(f"sifa stale-nag chat={chat_id} holder={nag_name!r} +notify")
            except Exception as e:
                logline(f"sifa stale-nag chat={chat_id}, но уведомление не ушло: {e!r}")
        if stale:
            logline(f"sifa chat={chat_id}: удалены неактивные касатки {stale}")


def poop_speed_km_per_min(poop: dict) -> float:
    """Скорость какашки: как у писем; адресат из LETTER_FAST_SENDERS — ускоренно."""
    if poop.get("chat") == GEO2_CHAT_ID:
        return SANDBOX_FAST_KM_PER_MIN
    mult = LETTER_FAST_SENDERS.get(poop["to"])
    return POOP_SPEED_KM_PER_MIN * mult if mult else POOP_SPEED_KM_PER_MIN


def poop_progress(poop: dict):
    """Текущая позиция розовой какашки (по прямой) и флаг прибытия."""
    total = haversine_km(poop["from_lat"], poop["from_lon"], poop["to_lat"], poop["to_lon"])
    elapsed_min = (time.time() - poop["start_ts"]) / 60.0
    done_km = min(elapsed_min * poop_speed_km_per_min(poop), total)
    frac = done_km / total if total > 0 else 1.0
    lat = poop["from_lat"] + (poop["to_lat"] - poop["from_lat"]) * frac
    lon = poop["from_lon"] + (poop["to_lon"] - poop["from_lon"]) * frac
    return lat, lon, total <= 0 or done_km >= total


def tg_send_message(chat_id: int, text: str) -> None:
    """Отправить сообщение в чат напрямую через Bot API (вызывается из HTTP-потока)."""
    req = urllib.request.Request(
        f"https://api.telegram.org/bot{BOT_TOKEN}/sendMessage",
        data=json.dumps({"chat_id": chat_id, "text": text}).encode("utf-8"),
        headers={"Content-Type": "application/json"}, method="POST",
    )
    urllib.request.urlopen(req, timeout=15).read()


ARRIVAL_NOTIFY_TTL_SEC = 3600  # уведомления о прибытии писем/какашек удаляются через час


def tg_mention(tid, name: str) -> str:
    """HTML-упоминание пользователя: tg://user?id=... — Telegram подсвечивает имя
    и показывает получателю «вас отметили» (работает даже без @username)."""
    return f'<a href="tg://user?id={int(tid)}">{html.escape(str(name))}</a>'


def geo_mention(chat_id, user_key, fallback: str) -> str:
    """Имя игрока для персонального уведомления: тег-упоминание, если у метки
    есть tid, иначе просто актуальное имя с метки (или fallback без tid)."""
    m = (geo_state.get(chat_id) or {}).get(user_key)
    if not m:
        return fallback
    name = m.get("name") or fallback
    tid = m.get("tid")
    if tid:
        try:
            return tg_mention(int(tid), name)
        except (TypeError, ValueError):
            return name
    return name


def _ws_tg_mention(chat_id: int, uid) -> str:
    """Упоминание по числовому id Telegram: имя из базы чата (tgids) + tg-ссылка."""
    info = ((tgids_state.get(str(chat_id)) or tgids_state.get(chat_id) or {})
            .get(str(uid), {}))
    return tg_mention(int(uid), info.get("name") or f"игрок {uid}")


async def weekly_stats_job(context) -> None:
    """Пятница 16:00 МСК: итоги недели в «Другое измерение» по 11 номинациям.
    Сообщение НЕ удаляется. Пустая номинация — красный крест (✗)."""
    chat_id = WEEKLY_STATS_CHAT
    now = time.time()
    markers = geo_state.get(chat_id) or {}
    members = set((tgids_state.get(str(chat_id)) or tgids_state.get(chat_id) or {}).keys())
    lines = ["🏆 <b>Итоги недели в «Другом измерении»</b>", ""]

    def row(emoji: str, title: str, desc: str, val, who) -> None:
        if val and who:
            lines.append(f"{emoji} <b>{title}</b> — {desc}: <b>{val}</b> — {who}")
        else:
            lines.append(f"{emoji} <b>{title}</b> — {desc}: ✗")

    def top(counter: dict):
        if not counter:
            return 0, None
        k, v = max(counter.items(), key=lambda kv: kv[1])
        return (v, k) if v and v > 0 else (0, None)

    try:
        # 1. Быки и коровы: победы (стата глобальная — берём участников этого чата)
        v, k = top({str(u): s.get("wins", 0) for u, s in stats.items()
                    if str(u) in members})
        row("🐂", "Быкующий гений", "побед в «Быки и коровы»", v,
            _ws_tg_mention(chat_id, k) if k else None)

        # 2. СагаЧат: написано глав (счётчик копится с момента обновления)
        saga = saga_state.get(chat_id) or {}
        v, k = top({u: n for u, n in (saga.get("author_counts") or {}).items()
                    if str(u) in members})
        row("📜", "Главный главописец", "глав в СагаЧате", v,
            _ws_tg_mention(chat_id, k) if k else None)

        # 3–4. Письма: отправлено / получено
        sent, got = {}, {}
        for l in letters_state.values():
            if l.get("chat") == chat_id:
                sent[l["from"]] = sent.get(l["from"], 0) + 1
                got[l["to"]] = got.get(l["to"], 0) + 1
        v, k = top(sent)
        row("✉️", "Почтмейстер", "отправлено писем", v,
            geo_mention(chat_id, k, k) if k else None)
        v, k = top(got)
        row("📥", "Магнит для писем", "получено писем", v,
            geo_mention(chat_id, k, k) if k else None)

        # 5. Розовые какашки: получено
        poops_got = {}
        for p in poops_state.values():
            if p.get("chat") == chat_id:
                poops_got[p["to"]] = poops_got.get(p["to"], 0) + 1
        v, k = top(poops_got)
        row("💗", "Розовощёкий", "получено розовых какашек", v,
            geo_mention(chat_id, k, k) if k else None)

        # 6. Подарки: получено
        gifts_got = {}
        for g in gifts_state.values():
            if g.get("chat") == chat_id:
                gifts_got[g["to"]] = gifts_got.get(g["to"], 0) + 1
        v, k = top(gifts_got)
        row("🎁", "Любимчик Дедморозов", "получено подарков", v,
            geo_mention(chat_id, k, k) if k else None)

        # 7. Звёздная пыль: собрано (агрегируем все ключи баланса в канонический ключ метки)
        pref = f"{chat_id}|"
        dust = {}
        for key, n in stardust_state.items():
            if not str(key).startswith(pref):
                continue
            ukey = str(key)[len(pref):]
            if str(ukey).isdigit():
                mk = next((mk for mk, m in markers.items()
                           if str(m.get("tid", "")) == str(ukey)), None)
                if mk:
                    ukey = mk
            dust[ukey] = dust.get(ukey, 0) + n
        v, k = top(dust)
        row("✨", "Звездочёт", "собрано звёздной пыли", v,
            geo_mention(chat_id, k, k) if k else None)

        # 8–9. Абордажи: потоплено галеонов / поражений (счётчики навсегда на метках)
        won = {mk: m["ships_won"] for mk, m in markers.items() if m.get("ships_won")}
        lost = {mk: m["ships_lost"] for mk, m in markers.items() if m.get("ships_lost")}
        v, k = top(won)
        row("⚔️", "Морской дьявол", "потоплено галеонов (мастер КНБ)", v,
            geo_mention(chat_id, k, k) if k else None)
        v, k = top(lost)
        row("🌊", "Корм для акул", "поражений при абордаже", v,
            geo_mention(chat_id, k, k) if k else None)

        # 10. Морской Рынок: часов владения (накопитель + текущий отсчёт)
        mk_e = market_state.get(str(chat_id)) or market_state.get(chat_id) or {}
        hours = dict(mk_e.get("owner_hours") or {})
        cur = mk_e.get("owner")
        if cur and mk_e.get("captured_ts"):
            hours[cur] = hours.get(cur, 0.0) + max(
                0.0, now - float(mk_e["captured_ts"])) / 3600.0
        v, k = top(hours)
        row("⚖️", "Воротила Рынка", "часов владения Морским Рынком",
            (round(v, 1) if v else 0), geo_mention(chat_id, k, k) if k else None)

        # 11. Сифа: сколько раз носил титул (счётчик копится с момента обновления)
        sifa_e = sifa_state.get(chat_id) or {}
        ships = sifa_e.get("ships") or {}
        v, k = top(sifa_e.get("sifa_holds") or {})
        who = None
        if k:
            tid = (ships.get(k) or {}).get("tid")
            nm = (ships.get(k) or {}).get("name") or k
            if tid:
                try:
                    who = tg_mention(int(tid), nm)
                except (TypeError, ValueError):
                    who = geo_mention(chat_id, k, nm)
            else:
                who = geo_mention(chat_id, k, nm)
        row("🐬", "Сифа недели", "раз получал титул Сифы", v, who)

        # 12. Клады: найдено (счётчик копится с введения квеста)
        kl = klad_state.get(chat_id) or {}
        v, k = top(kl.get("founds") or {})
        row("🏴‍☠️", "Величайший следопыт", "найдено кладов", v,
            geo_mention(chat_id, k, k) if k else None)
    except Exception as e:
        logline(f"weekly_stats: ошибка сбора статистики: {e!r}")
        return

    try:
        await context.bot.send_message(
            chat_id, "\n".join(lines), parse_mode="HTML",
            disable_web_page_preview=True)
        logline("weekly_stats: итоги недели отправлены")
    except Exception as e:
        logline(f"weekly_stats: не отправлена: {e!r}")


def tg_send_message_id(chat_id: int, text: str, html_mode: bool = False):
    """Отправить сообщение и вернуть message_id (None при ошибке).
    html_mode=True — текст в HTML (нужен для tg_mention)."""
    try:
        payload = {"chat_id": chat_id, "text": text}
        if html_mode:
            payload["parse_mode"] = "HTML"
        req = urllib.request.Request(
            f"https://api.telegram.org/bot{BOT_TOKEN}/sendMessage",
            data=json.dumps(payload).encode("utf-8"),
            headers={"Content-Type": "application/json"}, method="POST",
        )
        resp = json.loads(urllib.request.urlopen(req, timeout=15).read())
        return resp.get("result", {}).get("message_id")
    except Exception as e:
        print(f"[paint_bot] send_message не ушёл: {e!r}", flush=True)
        return None


def tg_delete_message(chat_id: int, msg_id: int) -> None:
    """Удалить сообщение напрямую через Bot API."""
    try:
        req = urllib.request.Request(
            f"https://api.telegram.org/bot{BOT_TOKEN}/deleteMessage",
            data=json.dumps({"chat_id": chat_id, "message_id": msg_id}).encode("utf-8"),
            headers={"Content-Type": "application/json"}, method="POST",
        )
        urllib.request.urlopen(req, timeout=15).read()
    except Exception as e:
        print(f"[paint_bot] не смог удалить сообщение {chat_id}/{msg_id}: {e!r}", flush=True)


def tg_send_with_cleanup(chat_id: int, text: str, ttl_sec: int,
                         html_mode: bool = False) -> None:
    """Отправить уведомление и автоудалить его через ttl_sec (из HTTP-потока).
    html_mode=True — для текстов с tg_mention (тег-упоминание)."""
    msg_id = tg_send_message_id(chat_id, text, html_mode=html_mode)
    if msg_id is not None:
        threading.Timer(ttl_sec, tg_delete_message, args=(chat_id, msg_id)).start()


def white_png() -> bytes:
    """Чистый белый лист 900×900 в PNG."""
    img = Image.new("RGB", (900, 900), "white")
    buf = io.BytesIO()
    img.save(buf, "PNG")
    return buf.getvalue()


# Сколько секунд замок «Рисует...» держится без отправки рисунка
PAINT_LOCK_TIMEOUT = 60
# Час бездействия с рисунком — лист автоматически «уходит в музей»
PAINT_IDLE_TIMEOUT = 3600


def new_paint_state() -> dict:
    return {
        "image": white_png(),
        "msg_id": None,
        "webapp": False,
        "drawer": None,  # имя того, кто сейчас рисует (мягкая очередь)
        "lock_time": 0.0,
        "last_activity": None,  # когда последний раз открывали холст/сохраняли рисунок
        "dirty_img": False,  # картинка менялась с последней отправки в чат
        "rendered_drawer": None,  # чей замок отображён на сообщении сейчас
    }


# ---------- Веб-часть: проверка живости, страница рисования, сохранение ----------

HTML_PAGE = """<!DOCTYPE html>
<html lang="ru">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, user-scalable=no">
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<style>
  body { margin:0; font-family:sans-serif; background:#f0f0f0; }
  #wrap { padding:8px; }
  canvas { width:100%; background:#fff; border:1px solid #ccc; border-radius:8px; touch-action:none; display:block; }
  .bar { display:flex; flex-wrap:wrap; gap:6px; margin-top:8px; align-items:center; }
  .sw { width:34px; height:34px; border-radius:50%; border:2px solid #999; }
  .sw.on { border-color:#000; transform:scale(1.15); }
  button { padding:10px 14px; border-radius:8px; border:none; font-size:15px; }
  #send { background:#2ea6ff; color:#fff; flex:1; }
  #clear { background:#ddd; }
  #status { margin-top:6px; color:#555; font-size:14px; min-height:18px; }
</style>
</head>
<body>
<div id="wrap">
  <canvas id="c"></canvas>
  <div class="bar">
    <input id="name" placeholder="Твоё имя" maxlength="24"
           style="flex:1;padding:10px;border-radius:8px;border:1px solid #ccc;font-size:15px;">
  </div>
  <div class="bar" id="colors"></div>
  <div class="bar">
    <button id="small">Тонко</button>
    <button id="mid">Средне</button>
    <button id="big">Толсто</button>
    <button id="eraser">Ластик</button>
    <button id="clear">Очистить</button>
  </div>
  <div class="bar">
    <button id="send">✅ Отправить в чат</button>
  </div>
  <div id="status"></div>
</div>
<script>
  const tg = window.Telegram.WebApp;
  tg.ready(); tg.expand();
  const chat = new URLSearchParams(location.search).get('chat') || '0';

  // все POST-запросы подписываем initData Telegram — сервер принимает действия только из TG
  const _origFetch = window.fetch.bind(window);
  window.fetch = (url, opts) => {
    opts = Object.assign({}, opts, {headers: Object.assign({}, opts && opts.headers,
      {'X-TG-Init-Data': tg.initData || ''})});
    return _origFetch(url, opts);
  };

  const COLORS = ['black','red','orange','yellow','green','blue','purple','brown'];
  const canvas = document.getElementById('c');
  const ctx = canvas.getContext('2d');
  canvas.width = 900; canvas.height = 900;
  let color = 'black', size = 6, drawing = false, last = null;

  // подгружаем текущий общий лист
  const img = new Image();
  img.onload = () => { ctx.drawImage(img, 0, 0, 900, 900); };
  img.src = '/canvas?chat=' + chat + '&t=' + Date.now();

  const status = (t) => document.getElementById('status').textContent = t;

  // имя рисующего: из Telegram (если WebApp) или из памяти браузера
  const nameInput = document.getElementById('name');
  const tgUser = (tg.initDataUnsafe && tg.initDataUnsafe.user) || null;
  nameInput.value = localStorage.getItem('paint_name')
    || (tgUser && (tgUser.username ? '@' + tgUser.username : tgUser.first_name)) || '';
  const userName = () => nameInput.value.trim() || 'Аноним';
  const begin = () => fetch('/begin?chat=' + chat + '&user=' + encodeURIComponent(userName())).catch(() => {});
  window.addEventListener('load', begin);
  nameInput.onchange = () => { localStorage.setItem('paint_name', nameInput.value.trim()); begin(); };
  window.addEventListener('beforeunload', () => {
    fetch('/end?chat=' + chat + '&user=' + encodeURIComponent(userName()), {keepalive: true}).catch(() => {});
  });

  // палитра
  const bar = document.getElementById('colors');
  COLORS.forEach(c => {
    const b = document.createElement('button');
    b.className = 'sw' + (c === color ? ' on' : '');
    b.style.background = c;
    b.onclick = () => {
      color = c; size = size === 30 ? 6 : size;
      document.querySelectorAll('.sw').forEach(x => x.classList.remove('on'));
      b.classList.add('on');
    };
    bar.appendChild(b);
  });
  document.getElementById('small').onclick = () => size = 4;
  document.getElementById('mid').onclick = () => size = 10;
  document.getElementById('big').onclick = () => size = 22;
  document.getElementById('eraser').onclick = () => { color = 'white'; size = 30; };
  document.getElementById('clear').onclick = () => { ctx.fillStyle = 'white'; ctx.fillRect(0, 0, 900, 900); };

  function pos(e) {
    const r = canvas.getBoundingClientRect();
    return [(e.clientX - r.left) * 900 / r.width, (e.clientY - r.top) * 900 / r.height];
  }
  function draw(a, b) {
    ctx.strokeStyle = color; ctx.lineWidth = size; ctx.lineCap = 'round'; ctx.lineJoin = 'round';
    ctx.beginPath(); ctx.moveTo(a[0], a[1]); ctx.lineTo(b[0], b[1]); ctx.stroke();
  }
  canvas.onpointerdown = (e) => { drawing = true; last = pos(e); canvas.setPointerCapture(e.pointerId); };
  canvas.onpointermove = (e) => { if (!drawing) return; const p = pos(e); draw(last, p); last = p; };
  canvas.onpointerup = () => drawing = false;

  document.getElementById('send').onclick = () => {
    status('Отправляю…');
    fetch('/save?chat=' + chat, {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({img: canvas.toDataURL('image/png')})
    }).then(r => {
      if (r.ok) { status('✅ Отправлено! Можно закрыть.'); setTimeout(() => tg.close(), 1200); }
      else status('Ошибка отправки, попробуй ещё раз.');
    }).catch(() => status('Нет сети, попробуй ещё раз.'));
  };
</script>
</body>
</html>"""


# === ГеографияЧата 2.0 — новая оболочка (тот же API; бета только для Песочницы) ===

GEO2_HTML_PAGE = io.open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                              "geo2.html"), encoding="utf-8").read()
# GEO2-страница вынесена в geo2.html (рядом с bot.py) — правки JS дешевле,
# py_compile не гоняется ради изменений в HTML


# ---------- Страница «География чата» (Leaflet + OpenStreetMap) ----------

BUILD_TAG = "2026-11-09-2155"  # менять при каждом деплое — диагностика, что на Render свежий код

GEO_HTML_PAGE = """<!DOCTYPE html>
<!-- build:2026-11-02-1519 -->
<html lang="ru">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, user-scalable=no">
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css">
<script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script>
<style>
  body { margin:0; font-family:sans-serif; background:#f0f0f0; }
  #map { width:100%; height:72vh; }
  .bar { padding:8px; display:flex; flex-wrap:wrap; gap:6px; align-items:center; }
  input { flex:1; min-width:140px; padding:10px; border-radius:8px; border:1px solid #ccc; font-size:15px; }
  button { padding:10px 14px; border-radius:8px; border:none; font-size:15px; background:#2ea6ff; color:#fff; }
  #status { padding:0 8px; color:#555; font-size:14px; min-height:18px; }
  .an { font-size:24px; background:#fff; border:2px solid #ddd; border-radius:8px; padding:4px 8px; cursor:pointer; }
  .an.on { border-color:#e05a3a; background:#ffe9e2; transform:scale(1.12); }
  .emoji-marker { background:none; border:none; }
</style>
</head>
<body>
<div id="map"></div>
<div class="bar" id="animals"></div>
<div class="bar">
  <input id="name" placeholder="Твоё имя" maxlength="24">
  <button id="delBtn" title="Удалить мою метку" style="display:none;background:#c0392b;">🗑</button>
  <button id="saveBtn">📍 Поставить метку</button>
  <button id="distBtn" style="background:#888;">📏 Расстояние</button>
  <button id="letterBtn" style="background:#888;">✉️ Письмо</button>
  <button id="islandBuyBtn" style="background:#888;">🏝️ Купить остров</button>
</div>
<div class="bar" id="letterBar" style="display:none;">
  <input id="letterText" placeholder="Текст письма (до 500 символов)" maxlength="500" style="flex:2;">
  <button id="letterSend">Отправить</button>
  <button id="letterCancel" style="background:#ddd;color:#333;">Отмена</button>
</div>
<div id="status"></div>
<script>
  const tg = window.Telegram.WebApp;
  tg.ready(); tg.expand();
  const chat = new URLSearchParams(location.search).get('chat') || '0';

  const map = L.map('map').setView([55, 45], 3);
  L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png',
    {maxZoom: 18, attribution: '© OpenStreetMap'}).addTo(map);
  const status = t => document.getElementById('status').textContent = t;
  const escapeHtml = s => { const d = document.createElement('div'); d.textContent = s; return d.innerHTML; };

  const tgUser = (tg.initDataUnsafe && tg.initDataUnsafe.user) || null;
  const nameInput = document.getElementById('name');
  nameInput.value = localStorage.getItem('geo_name')
    || (tgUser && (tgUser.username ? '@' + tgUser.username : tgUser.first_name)) || '';
  // гость вне Telegram: свой случайный ключ в этом браузере — не чужой и не общий «anon»
  let guestKey = localStorage.getItem('geo_guest');
  if (!guestKey) {
    guestKey = 'guest' + Math.random().toString(36).slice(2, 10);
    localStorage.setItem('geo_guest', guestKey);
  }
  const userKey = () => String((tgUser && tgUser.id) || nameInput.value.trim() || guestKey);
  const userName = () => (tgUser && (tgUser.username ? '@' + tgUser.username : tgUser.first_name))
    || nameInput.value.trim() || 'Гость';
  let serverMe = null;  // ключ моей метки, как его определил сервер по tid Telegram
  const myKey = () => serverMe || userKey();
  // все POST-запросы подписываем initData Telegram — сервер принимает действия только из TG
  const _origFetch = window.fetch.bind(window);
  window.fetch = (url, opts) => {
    opts = Object.assign({}, opts, {headers: Object.assign({}, opts && opts.headers,
      {'X-TG-Init-Data': tg.initData || ''})});
    return _origFetch(url, opts);
  };
  if (!tgUser) {
    // прямой заход в браузере — игра доступна только из под Телеграм
    const ov = document.createElement('div');
    ov.style.cssText = 'position:fixed;inset:0;z-index:99999;background:rgba(16,28,44,.94);'
      + 'display:flex;align-items:center;justify-content:center;text-align:center;'
      + 'color:#fff;font-size:19px;line-height:1.8;padding:24px;';
    ov.innerHTML = '<div>🗺️<br>Запустите, пожалуйста, игру из под Телеграм —<br>'
      + 'кнопкой меню бота в чате.<br>'
      + '<small style="opacity:.7">В браузере карта доступна только для просмотра.</small></div>';
    document.body.appendChild(ov);
  }

  let pending = null;
  const markers = {};  // user_key -> L.marker

  // выбор животного для метки (🐼 и 🐉 — персональные, в общий список не входят)
  const ANIMALS = ['🦊', '🦁', '🐸', '🐙', '🦉', '🐢', '🦖', '🐧', '🦄', '🐝', '🦔',
    '🐯', '🐨', '🐰', '🐻', '🐺', '🦩', '🐬', '🦒', '🐘', '🦅'];
  let curIcon = ANIMALS[0];
  const animalsBar = document.getElementById('animals');
  ANIMALS.forEach((a, i) => {
    const b = document.createElement('button');
    b.className = 'an' + (i === 0 ? ' on' : '');
    b.textContent = a;
    b.onclick = () => {
      curIcon = a;
      document.querySelectorAll('.an').forEach(x => x.classList.remove('on'));
      b.classList.add('on');
    };
    animalsBar.appendChild(b);
  });

  function animalIcon(emoji) {
    return L.divIcon({
      html: '<div style="font-size:28px;line-height:1;filter:drop-shadow(0 1px 2px rgba(0,0,0,.4))">' + emoji + '</div>',
      className: 'emoji-marker',
      iconSize: [36, 36], iconAnchor: [18, 18], popupAnchor: [0, -14],
    });
  }

  function renderMarker(m) {
    const emoji = m.icon || '📍';
    const mk = L.marker([m.lat, m.lon], {icon: animalIcon(emoji)}).addTo(map);
    let html = '<span style="font-size:22px">' + emoji + '</span> <b>' + escapeHtml(m.name) + '</b><br>'
      + m.lat.toFixed(3) + ', ' + m.lon.toFixed(3);
    // локальное время: по долготе от Москвы; у некоторых меток — своя «родная» зона
    const TIME_OVERRIDES = {'Андрюха': [-6, 'UTC−3'], 'Ice': [-1, 'UTC+2']};
    const ovr = TIME_OVERRIDES[m.name];
    let tLocal, tzLabel;
    if (ovr) {
      tLocal = new Date(Date.now() + ovr[0] * 3600000);
      tzLabel = ovr[1];
    } else {
      const tzShift = Math.round((m.lon - 37.6173) / 15);
      tLocal = new Date(Date.now() + (3 + tzShift) * 3600000);
      tzLabel = 'МСК' + (tzShift >= 0 ? '+' : '−') + Math.abs(tzShift);
    }
    const hh = String(tLocal.getUTCHours()).padStart(2, '0');
    const mm = String(tLocal.getUTCMinutes()).padStart(2, '0');
    html += '<br>🕒 ' + hh + ':' + mm + ' (' + tzLabel + ')';
    if (m.poops && m.user !== myKey()) html += '<br>💩 розовых какашек: ' + m.poops;
    if (m.gift_pics && m.gift_pics.length) html += '<br>🎁 подарки: ' + m.gift_pics.join(' ');
    if (m.souvenirs && m.souvenirs.length) html += '<br>🏝️ сувениры: ' + m.souvenirs.join(' ');
    if (m.user === myKey()) {
      const got = m.got || 0, read = m.read || 0;
      html += '<br><i>📮 письма — в Почтовом Ящике рядом с меткой</i>'
        + '<br>📬 получено ' + got + ' • прочитано ' + read + ' • непрочитано ' + (got - read)
        + '<br><br>☄️ моя ЗвезднаяПыль: <b>' + (m.zp || 0) + '</b>'
        + '<br>💩 мои Какашки: <b>' + (m.poops || 0) + '</b>';
      const myIsl = (lastIslands || []).find(i => (i.owners || [i.owner]).indexOf(myKey()) >= 0);
      if (myIsl) {
        html += '<br>🏝️ мой остров: <b>' + escapeHtml(myIsl.name) + '</b> (уровень '
          + myIsl.level + ') — ищи 🏝️ на карте';
      }
    }
    mk.bindPopup(html);
    mk.on('click', () => {
      if (distMode) pickPoint(m);
      else if (letterMode) tryLetterTarget(m);
      else if (volcanoMode) pickVolcanoTarget(m);
      else if (subMode) pickSubTarget(m);
      else if (islandInvMode) pickIslandGuest(m);
    });
    markers[m.user] = mk;
  }

  // ---------- Письма ----------
  const letterMarkers = {};  // letter_id -> L.marker
  let lastLetters = [];      // последние полученные с сервера письма (для списка в карточке метки)
  let lastIslands = [];      // последние полученные с сервера острова (для открытки и инфо в метке)
  let lastMarkers = [];      // последние метки (для выбора гостя списком в попапе острова)
  function letterIcon(l) {
    // ✉️ в пути • 📬 доставлено, не прочитано • 📭 доставлено и прочитано
    const e = !l.arrived ? '✉️' : (l.read ? '📭' : '📬');
    return L.divIcon({
      html: '<div style="font-size:26px;line-height:1;filter:drop-shadow(0 1px 2px rgba(0,0,0,.45))">'
        + e + '</div>',
      className: 'emoji-marker',
      // якорь НИЖЕ иконки: письмо висит над меткой (зазор ~8px) и не перекрывает животное
      iconSize: [36, 36], iconAnchor: [18, 44], popupAnchor: [0, -44],
    });
  }
  function renderLetter(l) {
    // прибывшие письма маркеров не создают: их показывает почтовый ящик на метке адресата
    // (📬/📭 прямо на иконке) + ссылки «прочитать» в попапе самой метки
    if (l.arrived) return;
    const mk = L.marker([l.lat, l.lon], {icon: letterIcon(l)}).addTo(map);
    // кнопка ускорения — на любом письме в полёте (чужом и своём), любой пользователь
    const boostBtn = '<br><button onclick="boostLetter(&quot;' + l.id
      + '&quot;)">⏩ Ускорить (1 ЗП)</button>';
    if (l.mine) {
      mk.bindPopup('✉️ Твоё письмо ещё в пути к тебе…' + boostBtn);
    } else {
      mk.bindPopup('📨 Письмо в пути… (адресат: ' + escapeHtml(l.to_name) + ')' + boostBtn);
    }
    letterMarkers[l.id] = mk;
  }

  async function readLetter(id) {
    const r = await fetch('/georead', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey(), name: userName(), id: id})
    });
    const data = await r.json().catch(() => ({}));
    if (r.ok) {
      const mk = letterMarkers[id];
      if (mk) {
        mk.setIcon(letterIcon({arrived: true, read: true}));  // прочитано — сразу 📭
        mk.bindPopup('📬 Письмо от <b>' + escapeHtml(data.from) + '</b>:<br>'
          + '<span style="font-size:17px">«' + escapeHtml(data.text) + '»</span><br>'
          + '<i>Можно перечитывать</i>');
        mk.openPopup();
      }
      status('📬 Письмо от ' + data.from + ': «' + data.text + '»' + (data.re_read ? ' (перечитано)' : ''));
      openLetterModal(data);  // красивое окно «старого письма»
      if (!mk) load();  // читали через ссылку в попапе метки — сразу обновить ящик 📬→📭
    } else if (r.status === 409) {
      status('✉️ Письмо ещё в пути — придёт, прочитаешь 🙂');
    } else {
      status('⚠️ ' + (data.error || 'не получилось прочитать'));
      if (r.status === 404) load();
    }
  }
  window.readLetter = readLetter;

  // ---------- Почтовый Ящик: отдельный объект рядом с моей меткой ----------
  let mailboxMarker = null;
  function mailboxIcon(full) {
    // 📬 — есть непрочитанные, 📭 — пустой; письма в пути на ящик не влияют
    return L.divIcon({
      html: '<div style="font-size:26px;line-height:1;filter:drop-shadow(0 1px 2px rgba(0,0,0,.45))">'
        + (full ? '📬' : '📭') + '</div>',
      className: 'emoji-marker',
      iconSize: [34, 34], iconAnchor: [17, 17], popupAnchor: [0, -14],
    });
  }
  function renderMailbox(markersData) {
    if (mailboxMarker) { map.removeLayer(mailboxMarker); mailboxMarker = null; }
    const me = (markersData || []).find(m => m.user === myKey());
    if (!me) return;  // без своей метки ящика нет
    // только письма, доступные для чтения/перечитывания (удалённые сервером не приходят)
    const myMail = lastLetters.filter(l => l.mine && l.arrived);
    const latCos = Math.max(Math.cos(me.lat * Math.PI / 180), 0.3);
    const mk = L.marker([me.lat + 0.004, me.lon + 0.004 / latCos],
                        {icon: mailboxIcon(myMail.some(l => !l.read))}).addTo(map);
    let html = '<b>📮 Почтовый Ящик</b>';
    // группировка по отправителям (алфавит, рус.): строка «Письма от …» раскрывается по клику
    const bySender = {};
    myMail.forEach(l => { (bySender[l.from_name] = bySender[l.from_name] || []).push(l); });
    const senders = Object.keys(bySender).sort((a, b) => a.localeCompare(b, 'ru'));
    if (!senders.length) {
      html += '<br><i>пусто — писем нет</i>';
    }
    senders.forEach((name, i) => {
      const list = bySender[name].slice().sort((a, b) => ((a.read ? 1 : 0) - (b.read ? 1 : 0)));
      const fresh = list.filter(l => !l.read).length;
      html += '<br><a href="#" onclick="toggleMail(' + i + '); return false;"><b>✉️ Письма от '
        + escapeHtml(name) + '</b> (' + list.length + (fresh ? ', 🆕 ' + fresh + ' нов.' : '') + ')</a>';
      html += '<div id="mailgrp-' + i + '" style="display:none">';
      list.forEach(l => {
        html += '<br>&nbsp;&nbsp;<a href="#" onclick="readLetter(&quot;' + l.id
          + '&quot;); return false;"' + (l.read ? ' style="color:#999"' : '') + '>'
          + (l.read ? '📭 ' : '📬 🆕 <b>Новое</b> · ') + (l.date || '') + '</a>';
      });
      html += '</div>';
    });
    mk.bindPopup(html);
    mailboxMarker = mk;
  }
  window.toggleMail = i => {
    const el = document.getElementById('mailgrp-' + i);
    if (el) el.style.display = (el.style.display === 'none') ? 'block' : 'none';
  };

  // ---------- Окно «старого письма» (эстетика чтения) ----------
  let letterModal = null;
  function openLetterModal(data) {
    if (!letterModal) {
      letterModal = document.createElement('div');
      letterModal.style.cssText = 'position:fixed;inset:0;background:rgba(30,20,10,.55);'
        + 'display:none;align-items:center;justify-content:center;z-index:100000;padding:18px;';
      const paper = document.createElement('div');
      paper.style.cssText = 'background:#f8eeda;max-width:430px;width:100%;max-height:82vh;'
        + 'overflow:auto;padding:24px 28px;border-radius:3px;position:relative;'
        + 'box-shadow:0 12px 44px rgba(0,0,0,.55), inset 0 0 60px rgba(160,130,80,.18);'
        + 'border:1px solid #d9c79c;';
      const stamp = document.createElement('div');
      stamp.textContent = '📮';
      stamp.style.cssText = 'position:absolute;top:10px;right:14px;font-size:26px;opacity:.55;'
        + 'transform:rotate(8deg);';
      const body = document.createElement('div');
      body.id = 'letterModalBody';
      body.style.cssText = 'font-family:Georgia,"Times New Roman",serif;color:#4a3a20;'
        + 'font-size:16px;line-height:1.6;white-space:pre-wrap;';
      const closeBtn = document.createElement('button');
      closeBtn.textContent = 'Закрыть';
      closeBtn.style.cssText = 'margin-top:18px;background:#8b6f47;color:#fff7e6;border:none;'
        + 'border-radius:6px;padding:8px 20px;font-size:14px;cursor:pointer;font-family:inherit;';
      closeBtn.onclick = () => { letterModal.style.display = 'none'; };
      paper.appendChild(stamp);
      paper.appendChild(body);
      paper.appendChild(closeBtn);
      letterModal.appendChild(paper);
      letterModal.addEventListener('click', e => { if (e.target === letterModal) letterModal.style.display = 'none'; });
      document.body.appendChild(letterModal);
    }
    const body = document.getElementById('letterModalBody');
    body.innerHTML = '<div style="text-align:right;font-size:13px;color:#8a764e;font-style:italic">'
      + escapeHtml(data.date || '') + '</div>'
      + '<div style="margin:8px 0 2px;font-size:14px;color:#8a764e">✉️ От: <b>'
      + escapeHtml(data.from) + '</b></div>'
      + '<hr style="border:none;border-top:1px solid #cbb98d;margin:10px 0">'
      + '<div style="font-size:17px">' + escapeHtml(data.text) + '</div>'
      + '<hr style="border:none;border-top:1px solid #cbb98d;margin:12px 0">'
      + '<div style="text-align:right;font-style:italic;font-size:13px;color:#8a764e">'
      + (data.re_read ? 'перечитано 📭' : '🆕 новое письмо') + '</div>';
    // кнопка «Ответить» — в том же окне, ответ летит отправителю автоматически
    if (data.from_id && data.from_id !== myKey()) {
      const replyBtn = document.createElement('button');
      replyBtn.textContent = '✍️ Ответить';
      replyBtn.style.cssText = 'margin-top:14px;margin-right:10px;background:#6d8b47;'
        + 'color:#fff7e6;border:none;border-radius:6px;padding:8px 20px;font-size:14px;'
        + 'cursor:pointer;font-family:inherit;';
      replyBtn.onclick = () => showReplyForm(data);
      body.appendChild(replyBtn);
    }
    letterModal.style.display = 'flex';
  }

  // форма ответа внутри окна письма
  function showReplyForm(orig) {
    const body = document.getElementById('letterModalBody');
    body.innerHTML = '<div style="font-size:14px;color:#8a764e">✍️ Ответ для <b>'
      + escapeHtml(orig.from) + '</b></div>'
      + '<textarea id="replyText" maxlength="500" placeholder="Текст ответа (до 500 символов)"'
      + ' style="width:100%;min-height:110px;margin-top:10px;padding:8px;box-sizing:border-box;'
      + 'font-family:inherit;font-size:15px;background:#fffdf6;border:1px solid #cbb98d;'
      + 'border-radius:4px;color:#4a3a20;resize:vertical;"></textarea>'
      + '<div id="replyErr" style="color:#a33;font-size:13px;min-height:16px;margin-top:4px;"></div>';
    const sendBtn = document.createElement('button');
    sendBtn.textContent = '✉️ Отправить';
    sendBtn.style.cssText = 'margin-top:8px;margin-right:10px;background:#6d8b47;color:#fff7e6;'
      + 'border:none;border-radius:6px;padding:8px 20px;font-size:14px;cursor:pointer;font-family:inherit;';
    sendBtn.onclick = () => sendReply(orig);
    const backBtn = document.createElement('button');
    backBtn.textContent = 'Назад';
    backBtn.style.cssText = 'margin-top:8px;background:#b8a888;color:#fff7e6;border:none;'
      + 'border-radius:6px;padding:8px 20px;font-size:14px;cursor:pointer;font-family:inherit;';
    backBtn.onclick = () => openLetterModal(orig);
    body.appendChild(sendBtn);
    body.appendChild(backBtn);
    setTimeout(() => { const ta = document.getElementById('replyText'); if (ta) ta.focus(); }, 60);
  }

  async function sendReply(orig) {
    const ta = document.getElementById('replyText');
    const err = document.getElementById('replyErr');
    const text = (ta ? ta.value : '').trim();
    if (!text) { if (err) err.textContent = 'пустое письмо — напиши хоть пару слов 🙂'; return; }
    const r = await fetch('/geosend', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey(), name: userName(),
                            to_user: orig.from_id, text: text})
    });
    const data = await r.json().catch(() => ({}));
    const body = document.getElementById('letterModalBody');
    if (r.ok) {
      body.innerHTML = '<div style="text-align:center;padding:22px 0;font-size:17px">✅ Ответ отправлен!<br>'
        + '<small style="color:#8a764e">полетит ' + data.eta_min + ' мин — загляни в ящик позже</small></div>';
      status('✉️ Ответ ушёл к ' + orig.from + ' — прибудет через ~' + data.eta_min + ' мин');
      load();
      setTimeout(() => { if (letterModal) letterModal.style.display = 'none'; }, 1800);
    } else if (err) {
      err.textContent = '⚠️ ' + (data.error || 'не отправилось, попробуй ещё раз');
    }
  }

  // ---------- Ванильный Вулкан Какашек ----------
  let volcanoMarker = null;      // L.marker вулкана
  const poopMarkers = {};        // poop_id -> L.marker
  let volcanoMode = false;       // ожидание выбора метки-адресата

  function volcanoIcon() {
    // в 3 раза крупнее обычной метки (обычная — шрифт 28px)
    return L.divIcon({
      html: '<div style="font-size:84px;line-height:1;filter:drop-shadow(0 2px 4px rgba(0,0,0,.5))">🌋</div>',
      className: 'emoji-marker',
      iconSize: [108, 108], iconAnchor: [54, 54], popupAnchor: [0, -50],
    });
  }
  function renderVolcano(v) {
    if (volcanoMarker) { map.removeLayer(volcanoMarker); volcanoMarker = null; }
    const mk = L.marker([v.lat, v.lon], {icon: volcanoIcon()}).addTo(map);
    const left = Math.floor(v.remain_sec / 60) + ':' + String(v.remain_sec % 60).padStart(2, '0');
    const btn = v.used ? '' : '<br><button onclick="startVolcano()">💥 Извержение</button>';
    mk.bindPopup('<b>Ванильный Вулкан Какашек</b> 🌋<br>Извержений доступно: <b>'
      + (v.used ? 0 : 1) + '</b><br>Осталось: ' + left + btn
      + '<br><hr style="margin:6px 0;border:none;border-top:1px solid #ddd">'
      + '<small><b>Как пользоваться:</b> жми «💥 Извержение» и кликни метку '
      + 'другого участника — ему полетит Розовая Какашка 💩🩷 '
      + 'со скоростью писем.<br>На весь вулкан — одно извержение: '
      + 'кто успел первым, тот и изверг 🙂</small>');
    volcanoMarker = mk;
  }
  window.startVolcano = () => {
    if (volcanoMarker) volcanoMarker.closePopup();
    volcanoMode = true;
    status('🌋 Кликни метку ДРУГОГО участника — в него полетит Розовая Какашка');
  };
  async function pickVolcanoTarget(m) {
    volcanoMode = false;
    if (m.user === myKey()) { status('Выбери метку ДРУГОГО участника, а не свою 🙂'); return; }
    const r = await fetch('/volcano', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey(), to_user: m.user})
    });
    const data = await r.json().catch(() => ({}));
    if (r.ok) {
      status('💩 Розовая Какашка полетела к ' + m.name + '! Прибудет через ~' + data.eta_min + ' мин');
      load();
    } else {
      status('⚠️ ' + (data.error || 'вулкан не извергся'));
      if (r.status === 409 || r.status === 404) load();
    }
  }
  function poopIcon(p) {
    return L.divIcon({
      html: '<div style="font-size:26px;line-height:1;background:#ffb6d5;border:2px solid #ff69b4;'
        + 'border-radius:50%;padding:3px;filter:drop-shadow(0 1px 2px rgba(0,0,0,.45))">💩</div>',
      className: 'emoji-marker',
      // якорь НИЖЕ иконки: какашка висит над меткой, не перекрывая её (как письма)
      iconSize: [40, 40], iconAnchor: [20, 52], popupAnchor: [0, -52],
    });
  }
  function renderPoop(p) {
    const mk = L.marker([p.lat, p.lon], {icon: poopIcon(p)}).addTo(map);
    if (!p.arrived) {
      // до доставки адресат неизвестен никому — даже самому адресату
      mk.bindPopup(p.i_sent
        ? '💩 Твоя Розовая Какашка летит к <b>' + escapeHtml(p.to_name) + '</b>…'
        : '💩 Розовая Какашка в пути… (адресат: *****)');
    } else if (p.mine) {
      mk.bindPopup('💩 Тебе прилетела Розовая Какашка! Поздравляем 🩷😄');
    } else {
      mk.bindPopup('💩 Доставлено адресату');
    }
    poopMarkers[p.id] = mk;
  }

  // ---------- Похотливый Кит и подарки ----------
  let submarineMarker = null;      // L.marker лодки
  const giftMarkers = {};          // gift_id -> L.marker
  let subMode = false;             // ожидание выбора метки-адресата

  function submarineIcon() {
    // Похотливый Кит: одиночный эмодзи; 60px — чтобы читался не хуже прошлой волны (42px)
    return L.divIcon({
      html: '<div style="font-size:60px;line-height:1;filter:drop-shadow(0 2px 3px rgba(0,0,0,.5))">🐳</div>',
      className: 'emoji-marker',
      iconSize: [76, 76], iconAnchor: [38, 38], popupAnchor: [0, -42],
    });
  }
  function renderSubmarine(s) {
    if (submarineMarker) { map.removeLayer(submarineMarker); submarineMarker = null; }
    const mk = L.marker([s.lat, s.lon], {icon: submarineIcon()}).addTo(map);
    const left = Math.floor(s.remain_sec / 60) + ':' + String(s.remain_sec % 60).padStart(2, '0');
    const btn = s.used ? '' : '<br><button onclick="startSub()">🎁 Отправить подарок</button>';
    mk.bindPopup('<b>Похотливый Кит</b> 🐳<br>Подарков доступно: <b>'
      + (s.used ? 0 : 1) + '</b><br>Осталось: ' + left + btn
      + '<br><hr style="margin:6px 0;border:none;border-top:1px solid #ddd">'
      + '<small><b>Как пользоваться:</b> жми «🎁 Отправить подарок» и кликни метку '
      + 'другого участника — от Похотливого Кита к нему поплывёт подарок со скоростью '
      + 'розовых какашек. Когда прибудет, адресат откроет его и увидит сюрприз 🔞, '
      + 'а картинка добавится в инфо его метки (увидят все).<br>На всего кита — '
      + 'один подарок: кто успел первым, тот и отправил 🙂</small>');
    submarineMarker = mk;
  }
  window.startSub = () => {
    if (submarineMarker) submarineMarker.closePopup();
    subMode = true;
    status('🐳 Кликни метку ДРУГОГО участника — к нему поплывёт подарок от Похотливого Кита');
  };
  async function pickSubTarget(m) {
    subMode = false;
    if (m.user === myKey()) { status('Выбери метку ДРУГОГО участника, а не свою 🙂'); return; }
    const r = await fetch('/subgift', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey(), name: userName(), to_user: m.user})
    });
    const data = await r.json().catch(() => ({}));
    if (r.ok) {
      status('🎁 Подарок поплыл к ' + m.name + '! Прибудет через ~' + data.eta_min + ' мин');
      load();
    } else {
      status('⚠️ ' + (data.error || 'кит не отправил'));
      if (r.status === 409 || r.status === 404) load();
    }
  }
  function giftIcon() {
    // размер и якорь — как у розовой какашки: висит над меткой, не перекрывая животное
    return L.divIcon({
      html: '<div style="font-size:26px;line-height:1;background:#ffe0b3;border:2px solid #ff9d4d;'
        + 'border-radius:50%;padding:3px;filter:drop-shadow(0 1px 2px rgba(0,0,0,.45))">🎁</div>',
      className: 'emoji-marker',
      iconSize: [40, 40], iconAnchor: [20, 52], popupAnchor: [0, -52],
    });
  }
  function renderGift(g) {
    const mk = L.marker([g.lat, g.lon], {icon: giftIcon()}).addTo(map);
    if (!g.arrived) {
      // до доставки адресат неизвестен никому — даже самому адресату (как у какашек)
      mk.bindPopup(g.i_sent
        ? '🎁 Твой подарок летит к <b>' + escapeHtml(g.to_name) + '</b>…'
        : '🎁 Подарок в пути… (адресат: *****)');
    } else if (g.mine) {
      mk.bindPopup('🎁 Тебе доставил подарок Похотливый Кит!<br><b>Нажми на него, чтобы открыть</b>');
      mk.on('click', () => openGift(g.id));
    } else {
      mk.bindPopup('🎁 Подарок доставлен адресату, ждёт открытия');
    }
    giftMarkers[g.id] = mk;
  }
  async function openGift(id) {
    const r = await fetch('/subopen', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey(), name: userName(), id: id})
    });
    const data = await r.json().catch(() => ({}));
    if (r.ok) {
      const mk = giftMarkers[id];
      if (mk) {
        mk.bindPopup('🎁 Подарок от <b>' + escapeHtml(data.from) + '</b> открыт!<br>'
          + '<span style="font-size:26px">' + escapeHtml(data.picture) + '</span><br>'
          + '<i>Картинка добавлена в инфо твоей метки — её видят все 😏</i>');
        mk.openPopup();
      }
      status('🎁 Подарок от ' + data.from + ': ' + data.picture);
      // load() не дергаем сразу — иначе сотрёт маркер вместе с попапом;
      // при следующем автообновлении маркер снимется, а картинка останется в инфо метки
    } else {
      status('⚠️ ' + (data.error || 'не получилось открыть'));
    }
  }
  window.openGift = openGift;

  // ---------- Метеорит и ЗвезднаяПыль ----------
  const meteorMarkers = [];   // воронки (метеориты)
  function meteorIcon() {
    // размер аватара метки (шрифт 28px) — было в 2 раза крупнее, оказалось громоздко
    return L.divIcon({
      html: '<div style="font-size:28px;line-height:1;filter:drop-shadow(0 1px 2px rgba(0,0,0,.5))">💥</div>',
      className: 'emoji-marker',
      iconSize: [36, 36], iconAnchor: [18, 18], popupAnchor: [0, -18],
    });
  }
  function renderMeteor(m) {
    const mk = L.marker([m.lat, m.lon], {icon: meteorIcon()}).addTo(map);
    let html;
    if (m.fresh && m.zp) {
      html = '<b>☄️ Метеоритная воронка</b><br>Остаток ЗП: <b>1</b><br>'
        + '<button onclick="claimMeteor()">🌟 Забрать ЗП</button>';
    } else if (m.fresh) {
      html = '<b>☄️ Метеоритная воронка</b><br>Остаток ЗП: <b>0</b> (уже забрали)';
    } else {
      html = '💥 Древняя воронка от метеорита<br>Остаток ЗП: 0';
    }
    mk.bindPopup(html);
    meteorMarkers.push(mk);
  }
  window.claimMeteor = async () => {
    const r = await fetch('/meteor', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey()})
    });
    const data = await r.json().catch(() => ({}));
    if (r.ok) {
      status('🌟 +1 ЗвезднаяПыль! Баланс: ' + data.balance);
      load();
    } else {
      status('⚠️ ' + (data.error || 'пыль не забралась'));
      if (r.status === 404 || r.status === 409) load();
    }
  };
  window.boostLetter = async (id) => {
    const r = await fetch('/letterboost', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey(), name: userName(), id: id})
    });
    const data = await r.json().catch(() => ({}));
    if (r.ok) {
      status('⏩ Письмо продвинулось на ' + data.boost_km + ' км! Баланс ЗП: ' + data.balance);
      load();
    } else {
      status('⚠️ ' + (data.error || 'не ускорилось'));
      if (r.status === 409) load();
    }
  };

  // ---------- Острова: покупка, гости на самолёте, постройки, открытка ----------
  const islandMarkers = {};    // owner -> L.marker острова
  const planeMarkers = {};     // owner острова -> L.marker самолёта с гостем
  let islandInvMode = false;   // ожидание выбора метки-гостя
  const ISLAND_BUILDINGS = {
    hut:    ['🛖', 'Хижина',         2, 5,  0],
    bar:    ['🏖️', 'Пляжный бар',     3, 10, 0],
    statue: ['🗿', 'Статуя Какашки',  5, 15, 10],
    castle: ['🏰', 'Островной замок', 8, 30, 0],
  };

  function islandIcon() {
    // размер — как у вулкана: остров должен быть заметен на карте
    return L.divIcon({
      html: '<div style="font-size:56px;line-height:1;filter:drop-shadow(0 2px 3px rgba(0,0,0,.5))">🏝️</div>',
      className: 'emoji-marker',
      iconSize: [72, 72], iconAnchor: [36, 36], popupAnchor: [0, -40],
    });
  }
  function planeIcon() {
    return L.divIcon({
      html: '<div style="font-size:30px;line-height:1;filter:drop-shadow(0 1px 2px rgba(0,0,0,.5))">✈️</div>',
      className: 'emoji-marker',
      iconSize: [40, 40], iconAnchor: [20, 20], popupAnchor: [0, -22],
    });
  }
  function renderIsland(isl) {
    const mk = L.marker([isl.lat, isl.lon], {icon: islandIcon()}).addTo(map);
    const built = isl.buildings || [];
    let html = (isl.mine
        ? '<button onclick="delIsland()" title="Удалить остров" style="background:#c0392b;padding:0 7px;font-size:14px;">🗑</button> '
        : '')
      + '<span style="font-size:22px">🏝️</span> <b>' + escapeHtml(isl.name) + '</b>'
      + '<br>владелец: ' + escapeHtml(isl.owner_name)
      + '<br>уровень: <b>' + isl.level + '</b> (' + isl.xp + ' опыта) • гостей побывало: '
      + isl.visits + '<br>постройки: 🌴' + (built.length ? ' ' : ' (пока одна пальма)')
      + built.map(b => ISLAND_BUILDINGS[b] ? ISLAND_BUILDINGS[b][0] : '').join(' ');
    if (isl.guest) {
      const legTxt = {
        to_guest: '✈️ самолёт летит за гостем…',
        to_island: '✈️ гостя везут на остров…',
        staying: '😎 гость на острове: <b>' + escapeHtml(isl.guest.name) + '</b>',
        home: '✈️ гость улетает домой…',
      };
      html += '<br>' + (legTxt[isl.guest.leg] || '');
    }
    if (isl.mine) {
      html += '<br><button onclick="startIslandInvite(&quot;' + isl.owner + '&quot;)">✈️ Пригласить гостя</button>'
        + ' <button onclick="islandPoop()">💩 Удобрить (+1 опыт)</button>';
      html += '<br><b>строительство:</b>';
      Object.keys(ISLAND_BUILDINGS).forEach(bid => {
        const spec = ISLAND_BUILDINGS[bid];
        const price = spec[3] + ' ЗП' + (spec[4] ? ' + ' + spec[4] + ' 💩' : '');
        if (built.indexOf(bid) >= 0) {
          html += '<br>' + spec[0] + ' ' + spec[1] + ' — ✅ построено';
        } else if (isl.level < spec[2]) {
          html += '<br>' + spec[0] + ' ' + spec[1] + ' — 🔒 с ' + spec[2] + ' ур. (' + price + ')';
        } else {
          html += '<br>' + spec[0] + ' ' + spec[1] + ' (' + price + ') '
            + '<button onclick="islandBuild(&quot;' + bid + '&quot;)">Построить</button>';
        }
      });
      html += '<br><i>гость на острове: +1 опыт тебе, гостю — ЗП и сувенир 🎁</i>';
    }
    // «Улететь» — для того, кто сейчас гостит на острове, независимо от владения
    // (совладелец тоже может быть гостем — кнопка не должна теряться из-за isl.mine)
    if (isl.guest && isl.guest.user === myKey() && isl.guest.leg === 'staying') {
      html += '<br><button onclick="leaveIsland()">✈️ Улететь (домой)</button>';
    }
    html += '<br><button onclick="openIslandCard(&quot;' + isl.owner + '&quot;)">🖼 Открытка острова</button>';
    mk.bindPopup(html);
    islandMarkers[isl.owner] = mk;
  }
  function renderPlane(p) {
    const mk = L.marker([p.lat, p.lon], {icon: planeIcon()}).addTo(map);
    const legTxt = {
      to_guest: 'летит за гостем…',
      to_island: 'везёт гостя на остров…',
      home: 'везёт гостя домой…',
    };
    mk.bindPopup('✈️ Самолёт острова ' + (legTxt[p.leg] || '') + '<br>гость: '
      + escapeHtml(p.guest_name));
    planeMarkers[p.island] = mk;
  }

  // открытка острова: красивая картинка со сценой заката и постройками
  let islandCard = null;
  function openIslandCard(owner) {
    const isl = (lastIslands || []).find(i => i.owner === owner);
    if (!isl) return;
    if (islandCard) { map.closePopup(); islandCard.remove(); islandCard = null; }
    const built = isl.buildings || [];
    const spots = {
      hut: 'left:14%;bottom:38%;', bar: 'right:12%;bottom:34%;',
      statue: 'left:42%;bottom:56%;', castle: 'right:26%;bottom:50%;',
    };
    let bHtml = '';
    built.forEach(bid => {
      if (ISLAND_BUILDINGS[bid] && spots[bid]) {
        bHtml += '<div style="position:absolute;' + spots[bid]
          + 'font-size:34px;filter:drop-shadow(0 2px 2px rgba(0,0,0,.45))">'
          + ISLAND_BUILDINGS[bid][0] + '</div>';
      }
    });
    islandCard = document.createElement('div');
    islandCard.style.cssText = 'position:fixed;inset:0;display:flex;align-items:center;'
      + 'justify-content:center;z-index:100000;padding:18px;background:rgba(10,20,35,.6);';
    islandCard.innerHTML = '<div style="position:relative;width:100%;max-width:520px;height:340px;'
      + 'border-radius:14px;overflow:hidden;'
      + 'background:linear-gradient(180deg,#ff9a56 0%,#ffcf8f 32%,#7ec8e3 33%,#2f6fb2 100%);'
      + 'box-shadow:0 16px 50px rgba(0,0,0,.6);font-family:Georgia,serif">'
      + '<div style="position:absolute;top:24px;left:50%;transform:translateX(-50%);'
      + 'width:60px;height:60px;border-radius:50%;'
      + 'background:radial-gradient(circle,#fff3c4 0%,#ffd257 55%,rgba(255,180,60,0) 100%)"></div>'
      + '<div style="position:absolute;left:50%;bottom:38px;transform:translateX(-50%);'
      + 'font-size:120px;line-height:1;filter:drop-shadow(0 6px 6px rgba(0,0,0,.35))">🏝️</div>'
      + '<div style="position:absolute;left:20%;bottom:30px;font-size:36px;line-height:1">🌴</div>'
      + bHtml
      + '<div style="position:absolute;top:12px;left:0;right:0;text-align:center;color:#4a2c12;'
      + 'font-weight:bold;font-size:19px;text-shadow:0 1px 0 rgba(255,255,255,.6)">'
      + escapeHtml(isl.name) + '</div>'
      + '<div style="position:absolute;bottom:8px;left:0;right:0;text-align:center;color:#fff;'
      + 'font-size:13px;text-shadow:0 1px 3px rgba(0,0,0,.7)">уровень ' + isl.level
      + ' • опыт ' + isl.xp + ' • гостей побывало: ' + isl.visits
      + ' • владелец ' + escapeHtml(isl.owner_name) + '</div>'
      + '<button onclick="this.parentNode.parentNode.remove()" '
      + 'style="position:absolute;top:10px;right:12px;background:rgba(255,255,255,.85);'
      + 'border:none;border-radius:50%;width:30px;height:30px;font-size:15px;cursor:pointer">✕</button>'
      + '</div>';
    document.body.appendChild(islandCard);
  }
  window.openIslandCard = openIslandCard;

  window.buyIsland = async () => {
    const r = await fetch('/islandbuy', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey(), name: userName()})
    });
    const data = await r.json().catch(() => ({}));
    if (r.ok) {
      status('🏝️ Твой остров: «' + data.name + '»! Баланс ЗП: ' + data.balance);
      load();
    } else {
      status('⚠️ ' + (data.error || 'не получилось купить остров'));
    }
  };
  window.startIslandInvite = (owner) => {
    islandInvMode = true;  // клик по метке на карте тоже сработает
    const isl = (lastIslands || []).find(i => i.owner === owner);
    const mk = isl && islandMarkers[owner];
    if (!isl || !mk) { status('✈️ Кликни метку гостя, которого зовёшь на остров'); return; }
    // выбор гостя списком прямо в попапе — не нужно тыкать по карте
    const others = (lastMarkers || []).filter(xm => xm.user !== myKey());
    let html = '<b>✈️ Кого зовём на «' + escapeHtml(isl.name) + '»?</b>';
    if (!others.length) {
      html += '<br><i>кроме тебя в чате меток нет</i>';
    }
    others.forEach(xm => {
      html += '<br><button onclick="invitePick(&quot;' + encodeURIComponent(xm.user)
        + '&quot;,&quot;' + encodeURIComponent(xm.name) + '&quot;)">'
        + escapeHtml(xm.icon || '📍') + ' ' + escapeHtml(xm.name) + '</button>';
    });
    html += '<br><i>…или кликни метку гостя прямо на карте</i>';
    mk.bindPopup(html);
    mk.openPopup();
    status('✈️ Выбери гостя из списка на острове (или кликни его метку на карте)');
  };
  window.invitePick = (encUser, encName) => {
    pickIslandGuest({user: decodeURIComponent(encUser), name: decodeURIComponent(encName)});
  };
  async function pickIslandGuest(m) {
    islandInvMode = false;
    if (m.user === myKey()) { status('Выбери метку ДРУГОГО участника, а не свою 🙂'); return; }
    const r = await fetch('/islandinvite', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey(), to_user: m.user})
    });
    const data = await r.json().catch(() => ({}));
    if (r.ok) {
      status('✈️ Самолёт полетел за ' + data.guest_name + '! Прибудет примерно через '
        + data.eta_min + ' мин');
      load();
    } else {
      status('⚠️ ' + (data.error || 'не получилось позвать'));
      if (r.status === 404 || r.status === 409) load();
    }
  }
  window.leaveIsland = async () => {
    const r = await fetch('/islandleave', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey()})
    });
    const data = await r.json().catch(() => ({}));
    if (r.ok) {
      status('✈️ Улетаешь домой' + (data.gone ? '' : ' — прибудешь через ~' + data.eta_min + ' мин')
        + '. Спасибо за визит! 🙂');
    } else {
      status('⚠️ ' + (data.error || 'не улетелось'));
    }
    load();
  };
  window.islandBuild = async (bid) => {
    const r = await fetch('/islandbuild', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey(), building: bid})
    });
    const data = await r.json().catch(() => ({}));
    if (r.ok) {
      status('🏗 ' + data.emoji + ' «' + data.name + '» построено! Уровень острова: '
        + data.level + ' • баланс ЗП: ' + data.balance);
      load();
    } else {
      status('⚠️ ' + (data.error || 'не построилось'));
      if (r.status === 403 || r.status === 409) load();
    }
  };
  window.islandPoop = async () => {
    const r = await fetch('/islandpoop', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey()})
    });
    const data = await r.json().catch(() => ({}));
    if (r.ok) {
      status('💩 Удобрено! Опыт: ' + data.xp + ' (уровень ' + data.level
        + '), какашек осталось: ' + data.poops_left
        + ' — сегодня удобрено ' + data.poop_today + '/' + data.poop_limit);
      load();
    } else {
      status('⚠️ ' + (data.error || 'не удобрилось'));
      if (r.status === 403 || r.status === 404) load();
    }
  };
  window.delIsland = async () => {
    if (!confirm('Вы точно хотите удалить остров? Это навсегда!')) return;
    const r = await fetch('/islanddel', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey()})
    });
    const data = await r.json().catch(() => ({}));
    if (r.ok) {
      status('🏝️ Остров удалён — растворился в океане. Новый можно основать за 10 ЗП 🙂');
      load();
    } else {
      status('⚠️ ' + (data.error || 'не удалилось удалить остров'));
      if (r.status === 404 || r.status === 409) load();
    }
  };

  // ---------- Расстояние и время в пути (по прямой) ----------
  const toRad = d => d * Math.PI / 180;
  function haversineKm(a, b) {
    const R = 6371;
    const dLat = toRad(b.lat - a.lat), dLon = toRad(b.lon - a.lon);
    const s = Math.sin(dLat / 2) ** 2 + Math.cos(toRad(a.lat)) * Math.cos(toRad(b.lat)) * Math.sin(dLon / 2) ** 2;
    return 2 * R * Math.asin(Math.sqrt(s));
  }
  function fmtKm(km) { return km < 10 ? km.toFixed(1) + ' км' : Math.round(km).toLocaleString('ru-RU') + ' км'; }
  function fmtTime(km, speed) {
    const mins = Math.round(km / speed * 60);
    if (mins < 60) return mins + ' мин';
    const h = Math.floor(mins / 60), m = mins % 60;
    if (h < 24) return m ? h + ' ч ' + m + ' мин' : h + ' ч';
    return Math.floor(h / 24) + ' дн ' + (h % 24) + ' ч';
  }

  let distMode = false, letterMode = false, pointA = null, distLine = null;
  const distBtn = document.getElementById('distBtn');
  const letterBtn = document.getElementById('letterBtn');
  const letterBar = document.getElementById('letterBar');
  let letterTarget = null;
  function setMode(mode) {
    distMode = mode === 'dist';
    letterMode = mode === 'letter';
    pointA = null;
    if (distLine) { map.removeLayer(distLine); distLine = null; }
    distBtn.style.background = distMode ? '#e05a3a' : '#888';
    letterBtn.style.background = letterMode ? '#e05a3a' : '#888';
    if (!letterMode) { letterBar.style.display = 'none'; letterTarget = null; }
    status(distMode ? '📏 Кликни первую метку (или точку на карте), потом вторую'
      : letterMode ? '✉️ Кликни метку ДРУГОГО участника, чтобы отправить письмо'
      : 'Режим выключен');
  }
  distBtn.onclick = () => setMode(distMode ? null : 'dist');
  letterBtn.onclick = () => setMode(letterMode ? null : 'letter');
  document.getElementById('islandBuyBtn').onclick = () => buyIsland();

  function tryLetterTarget(m) {
    if (m.user === myKey()) { status('Выбери метку ДРУГОГО участника, а не свою 🙂'); return; }
    letterTarget = m;
    letterBar.style.display = 'flex';
    status('✉️ Письмо для ' + m.name + ' — напиши текст (до 500 символов)');
  }
  document.getElementById('letterCancel').onclick = () => setMode(null);
  document.getElementById('letterSend').onclick = async () => {
    const textEl = document.getElementById('letterText');
    const text = textEl.value.trim();
    if (!text) { status('Письмо пустое — напиши что-нибудь 🙂'); return; }
    if (!letterTarget) { setMode(null); return; }
    const target = letterTarget;
    const r = await fetch('/geosend', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey(), name: userName(),
                          to_user: target.user, text: text})
    });
    const data = await r.json().catch(() => ({}));
    if (r.ok) {
      textEl.value = '';
      setMode(null);
      status('✉️ Отправлено! Прибудет примерно через ' + data.eta_min + ' мин');
      load();
    } else if (r.status === 409) {
      status('⚠️ ' + (data.error || ('Уже есть письмо в пути к ' + target.name + ' — дождись доставки')));
    } else {
      status('⚠️ ' + (data.error || 'не отправилось'));
    }
  };

  function pickPoint(p) {
    if (!pointA) { pointA = p; status('📍 Точка А: ' + p.name + ' — теперь выбери вторую'); return; }
    if (haversineKm(pointA, p) < 0.05) { status('Это то же место — выбери другую точку'); return; }
    const km = haversineKm(pointA, p);
    if (distLine) map.removeLayer(distLine);
    distLine = L.polyline(
      [[pointA.lat, pointA.lon], [p.lat, p.lon]],
      {color: '#e05a3a', dashArray: '8 6', weight: 3}
    ).addTo(map);
    status('📏 ' + pointA.name + ' → ' + p.name + ': ' + fmtKm(km)
      + ' • 🚶 ' + fmtTime(km, 5)
      + ' • 🚗 ' + fmtTime(km, 80)
      + ' • ✈️ ' + fmtTime(km, 800) + ' (по прямой)');
    pointA = null;
  }

  // если метка уже поставлена — убираем инструменты постановки (эмодзи, кнопку, имя),
  // остаются только 📏 и ✉️; удаление метки вернёт всё обратно
  function updateMineUI() {
    const mine = !!markers[myKey()];
    document.getElementById('animals').style.display = mine ? 'none' : 'flex';
    document.getElementById('saveBtn').style.display = mine ? 'none' : '';
    document.getElementById('delBtn').style.display = mine ? '' : 'none';
    nameInput.disabled = mine;
    nameInput.title = mine ? 'Имя закреплено за твоей меткой. Удали метку (🗑 справа), чтобы изменить.' : '';
  }

  async function load() {
    const r = await fetch('/geodata?chat=' + chat + '&user=' + encodeURIComponent(myKey()) + '&name=' + encodeURIComponent(userName()) + '&t=' + Date.now());
    const data = await r.json();
    serverMe = data.me || null;
    if (data.viewer_admin === false && !document.getElementById('adminOv')) {
      const ov = document.createElement('div');
      ov.id = 'adminOv';
      ov.style.cssText = 'position:fixed;inset:0;z-index:99999;background:rgba(16,28,44,.94);'
        + 'display:flex;align-items:center;justify-content:center;text-align:center;'
        + 'color:#fff;font-size:19px;line-height:1.8;padding:24px;';
      ov.innerHTML = '<div>🛡️<br>Полный функционал игры доступен только админам '
        + 'этой группы.<br><small style="opacity:.7">Карта — для просмотра.</small></div>';
      document.body.appendChild(ov);
    }
    Object.values(markers).forEach(m => map.removeLayer(m));
    Object.keys(markers).forEach(k => delete markers[k]);
    Object.values(letterMarkers).forEach(m => map.removeLayer(m));
    Object.keys(letterMarkers).forEach(k => delete letterMarkers[k]);
    Object.values(poopMarkers).forEach(m => map.removeLayer(m));
    Object.keys(poopMarkers).forEach(k => delete poopMarkers[k]);
    Object.values(giftMarkers).forEach(m => map.removeLayer(m));
    Object.keys(giftMarkers).forEach(k => delete giftMarkers[k]);
    Object.values(islandMarkers).forEach(m => map.removeLayer(m));
    Object.keys(islandMarkers).forEach(k => delete islandMarkers[k]);
    Object.values(planeMarkers).forEach(m => map.removeLayer(m));
    Object.keys(planeMarkers).forEach(k => delete planeMarkers[k]);
    lastLetters = data.letters || [];
    lastIslands = data.islands || [];
    lastMarkers = data.markers || [];
    // кнопку покупки прячем, если остров уже есть (повторная покупка запрещена)
    const buyIslBtn = document.getElementById('islandBuyBtn');
    if (buyIslBtn) {
      const haveIsl = lastIslands.some(i => (i.owners || [i.owner]).indexOf(myKey()) >= 0);
      buyIslBtn.style.display = haveIsl ? 'none' : '';
    }
    meteorMarkers.forEach(m => map.removeLayer(m));
    meteorMarkers.length = 0;
    (data.markers || []).forEach(renderMarker);
    (data.letters || []).forEach(renderLetter);
    (data.poops || []).forEach(renderPoop);
    (data.meteors || []).forEach(renderMeteor);
    (data.islands || []).forEach(renderIsland);
    (data.planes || []).forEach(renderPlane);
    if (data.volcano) renderVolcano(data.volcano);
    else if (volcanoMarker) { map.removeLayer(volcanoMarker); volcanoMarker = null; }
    (data.gifts || []).forEach(renderGift);
    if (data.submarine) renderSubmarine(data.submarine);
    else if (submarineMarker) { map.removeLayer(submarineMarker); submarineMarker = null; }
    renderMailbox(data.markers);
    updateMineUI();
    // прибывших писем на карте нет (их показывает ящик на метке) — считаем только в пути
    const flyingLetters = (data.letters || []).filter(l => !l.arrived).length;
    status('🌍 Меток: ' + (data.markers || []).length + ' • ✉️ Писем в пути: '
      + flyingLetters
      + ' • 🏝️ Островов: ' + (data.islands || []).length
      + (data.volcano ? ' • 🌋 ВУЛКАН НА КАРТЕ!' : '')
      + (data.meteors && data.meteors.some(m => m.fresh && m.zp) ? ' • 💥 МЕТЕОРИТ!' : '')
      + (data.submarine && !data.submarine.used ? ' • 🐳 ПОХОТЛИВЫЙ КИТ В ОКЕАНЕ!' : ''));
  }
  setInterval(load, 60000);  // автообновление; позиции писем считает сервер по времени

  map.on('click', e => {
    if (distMode) {
      pickPoint({lat: e.latlng.lat, lon: e.latlng.lng, name: 'точка на карте'});
      return;
    }
    if (letterMode) { status('✉️ Кликни по МЕТКЕ участника (животное на карте), а не просто по карте'); return; }
    if (volcanoMode) { status('🌋 Кликни по МЕТКЕ участника (животное на карте), а не просто по карте'); return; }
    if (subMode) { status('🐳 Кликни по МЕТКЕ участника (животное на карте), а не просто по карте'); return; }
    if (islandInvMode) { status('✈️ Кликни по МЕТКЕ участника (животное на карте), а не просто по карте'); return; }
    if (markers[myKey()]) {
      status('У тебя уже есть метка. Чтобы поставить новую — кликни по своему животному и выбери «Удалить мою метку»');
      return;
    }
    pending = e.latlng;
    status('Точка: ' + e.latlng.lat.toFixed(4) + ', ' + e.latlng.lng.toFixed(4) + ' — жми «Поставить метку»');
  });

  document.getElementById('saveBtn').onclick = async () => {
    if (!pending) { status('Сначала кликни по карте в месте своего города'); return; }
    if (nameInput.value.trim()) localStorage.setItem('geo_name', nameInput.value.trim());
    const r = await fetch('/geomark', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey(), name: userName(), icon: curIcon,
                            lat: pending.lat, lon: pending.lng})
    });
    if (r.ok) { status('✅ Метка поставлена!'); pending = null; load(); }
    else status('Ошибка, попробуй ещё раз');
  };

  async function delMarker() {
    if (!confirm('Вы точно хотите удалить метку?')) return;
    await fetch('/geodel', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: myKey()})
    });
    load();
  }
  window.delMarker = delMarker;
  document.getElementById('delBtn').onclick = delMarker;

  nameInput.onchange = () => { localStorage.setItem('geo_name', nameInput.value.trim()); load(); };
  load();
</script>
</body>
</html>"""


# ---------- Кольцевой буфер последних логов (читается через GET /geologs) ----------

RECENT_LOGS: list[str] = []
TGINFO_KEY = "sumai-tginfo-2026"  # ключ для служебного эндпоинта /tginfo


def logline(msg: str) -> None:
    RECENT_LOGS.append(f"{datetime.datetime.now(MSK_TZ).strftime('%m-%d %H:%M:%S')} {msg}")
    if len(RECENT_LOGS) > 200:
        del RECENT_LOGS[:-200]
    print(f"[paint_bot] {msg}", flush=True)


class AppHandler(BaseHTTPRequestHandler):
    """HTTP-часть сервиса: / — проверка живости, /app — холст, /canvas — PNG, /save — приём рисунка."""

    def _respond(self, code, body=b"", ctype="text/plain; charset=utf-8", nocache=False):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        if nocache:
            # Telegram WebView агрессивно кэширует страницу приложения — без этого
            # старый JS живёт у пользователей после деплоя
            self.send_header("Cache-Control", "no-store, no-cache, must-revalidate")
            self.send_header("Pragma", "no-cache")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        url = urlparse(self.path)
        params = parse_qs(url.query)
        if url.path in ("/", ""):
            self._respond(200, "paint_bot is running".encode("utf-8"))
        elif url.path == "/geologs":
            # служебный: последние строки лога (читаемы без доступа к дашборду Render)
            self._respond(200, "\n".join(RECENT_LOGS[-100:]).encode("utf-8"))
        elif url.path == "/tginfo":
            # служебный (ключ): инфо о чате и список админов через Bot API —
            # нужен, потому что с рабочей сети api.telegram.org недоступен
            if params.get("key", [""])[0] != TGINFO_KEY:
                self._respond(403, b"forbidden")
                return
            chat_id = params.get("chat", [""])[0]
            out = {}
            try:
                req = urllib.request.Request(
                    f"https://api.telegram.org/bot{BOT_TOKEN}/getChat?chat_id={chat_id}")
                out["chat"] = json.load(urllib.request.urlopen(req, timeout=15)).get("result")
                req = urllib.request.Request(
                    f"https://api.telegram.org/bot{BOT_TOKEN}/getChatAdministrators?chat_id={chat_id}")
                out["admins"] = json.load(urllib.request.urlopen(req, timeout=15)).get("result")
            except Exception as e:
                out["error"] = repr(e)
            self._json_response(200, out)
        elif url.path == "/sendmsg":
            # служебный (ключ): отправка текста от имени бота в чат —
            # нужен, потому что с рабочей сети api.telegram.org недоступен
            if params.get("key", [""])[0] != TGINFO_KEY:
                self._respond(403, b"forbidden")
                return
            chat_id = int(params.get("chat", ["0"])[0])
            text = params.get("text", [""])[0]
            if chat_id not in ALLOWED_GROUPS:
                self._json_response(403, {"error": "chat not allowed"})
                return
            out = {"chat": chat_id, "text": text}
            try:
                data = urllib.parse.urlencode({"chat_id": chat_id, "text": text}).encode("utf-8")
                req = urllib.request.Request(
                    f"https://api.telegram.org/bot{BOT_TOKEN}/sendMessage",
                    data=data, method="POST")
                resp = json.load(urllib.request.urlopen(req, timeout=15))
                out["ok"] = resp.get("ok")
                out["result"] = resp.get("result", {}).get("message_id")
            except Exception as e:
                out["error"] = repr(e)
            self._json_response(200, out)
        elif url.path == "/sifaadmin":
            # служебный (ключ): сдвиг касатки пользователя на N км на восток —
            # починка «застрявших» касаток без перезапуска сервера
            if params.get("key", [""])[0] != TGINFO_KEY:
                self._respond(403, b"forbidden")
                return
            chat_id = int(params.get("chat", ["0"])[0])
            user = params.get("user", [""])[0][:64]
            km = float(params.get("km", ["0"])[0])
            out = {"chat": chat_id, "user": user, "km": km}
            try:
                with sifa_lock:
                    ship = (sifa_state.get(chat_id, {}).get("ships") or {}).get(user)
                    if ship is None:
                        out["error"] = "ship not found"
                    else:
                        dlon = km / (111.32 * math.cos(math.radians(ship["lat"])))
                        ship["lon"] = max(-180.0, min(180.0, ship["lon"] + dlon))
                        ship["ts"] = time.time()
                        sifa_save_to_github(force=True)
                        out.update({"ok": True, "lat": ship["lat"], "lon": ship["lon"]})
            except Exception as e:
                out["error"] = repr(e)
            self._json_response(200, out)
        elif url.path == "/islandimg":
            # арт острова и сооружений (файлы в репозитории рядом с bot.py)
            p = params.get("p", [""])[0]
            fn = {"base": ("island_base.jpg", "image/jpeg"),
                  "hut": ("island_hut.png", "image/png"),
                  "bar": ("island_bar.png", "image/png"),
                  "statue": ("island_statue.png", "image/png"),
                  "castle": ("island_castle.png", "image/png"),
                  "shipyard": ("island_shipyard.png", "image/png")}.get(p)
            if not fn:
                self._respond(404, b"no image")
                return
            try:
                fpath = os.path.join(os.path.dirname(os.path.abspath(__file__)), fn[0])
                with open(fpath, "rb") as f:
                    data = f.read()
                self._respond(200, data, fn[1])
            except Exception:
                self._respond(404, b"no image")
        elif url.path == "/shipimg":
            # картинки кораблей (встроены в код base64) — маркеры галеонов на карте
            data = GALLEON_SUNK_B64 if params.get("sunk") else GALLEON_B64
            if not data:
                self._respond(404, b"no image")
                return
            self._respond(200, base64.b64decode(data), "image/png")
        elif url.path == "/shipduel":
            # быстрый опрос дуэли КНБ (модалка абордажа)
            chat_id = int(params.get("chat", ["0"])[0])
            user = params.get("user", [""])[0][:64]
            name = params.get("name", [""])[0][:64]
            out = {}
            with geo_lock:
                me = ship_of(chat_id, user, name)
                if me:
                    duel_cleanup(time.time())
                    dv = duel_view_for(chat_id, me["user"], time.time())
                    if dv is not None:
                        out = public_duel(dv, me["user"])
            self._json_response(200, out)
        elif url.path == "/shipwatch":
            # зрительский вид дуэли КНБ (иконка сражения на карте)
            chat_id = int(params.get("chat", ["0"])[0])
            did = params.get("duel", [""])[0][:96]
            out = {}
            with geo_lock:
                d = ship_duels.get(did)
                if d is not None and d["chat"] == chat_id:
                    duel_tick(d, time.time())
                    if not (d["phase"] == "finished"
                            and time.time() - d.get("finished_ts", 0) > SHIP_DUEL_KEEP_SEC):
                        out = spectator_duel(d)
            self._json_response(200, out)
        elif url.path == "/app":
            self._respond(200, HTML_PAGE.encode("utf-8"), "text/html; charset=utf-8", nocache=True)
        elif url.path == "/canvas":
            chat_id = int(params.get("chat", ["0"])[0])
            state = paint_state.get(chat_id)
            self._respond(200, state["image"] if state else white_png(), "image/png")
        elif url.path == "/geomap":
            self._respond(200, GEO_HTML_PAGE.encode("utf-8"), "text/html; charset=utf-8", nocache=True)
        elif url.path == "/geo2map":
            # «ГеографияЧата 2.0» — Песочница и «Другое измерение». Без ?chat= тоже
            # отдаём страницу: прямой вход Mini App по t.me/<bot>/<shortname> приходит
            # без параметров — чат клиент берёт из start_param (initData).
            chat_param = params.get("chat", [""])[0]
            if chat_param and int(chat_param) not in (GEO2_CHAT_ID, ANON_GROUP_ID):
                self._respond(403, "beta: allowed chats only".encode("utf-8"),
                              "text/plain; charset=utf-8")
            else:
                self._respond(200, GEO2_HTML_PAGE.encode("utf-8"), "text/html; charset=utf-8", nocache=True)
        elif url.path == "/sifastate":
            chat_id = int(params.get("chat", ["0"])[0])
            viewer = params.get("user", [""])[0]
            viewer_name = params.get("name", [""])[0][:64]
            now = time.time()
            ships = []
            me = None
            area = None
            logs = []
            need_save = False
            with sifa_lock:
                entry = sifa_state.get(chat_id)
                if entry:
                    area = entry.get("area")
                    logs = entry.get("logs") or []
                    sk_viewer = resolve_ship_key(entry["ships"], viewer, viewer_name)
                    # плывущие брёвна: одно в случайной водной точке зоны — раз в 3 часа
                    nlt = entry.get("next_log_ts", 0)
                    if area and now >= nlt:
                        llat, llon = sifa_random_water(area)
                        logs = entry["logs"] = logs + [{"lat": round(llat, 6),
                                                        "lon": round(llon, 6)}]
                        entry["next_log_ts"] = now + SIFA_LOG_PERIOD_SEC
                        need_save = True
                    elif not area and not nlt:
                        entry["next_log_ts"] = now + SIFA_LOG_PERIOD_SEC
                    for u, s in list(entry["ships"].items()):
                        mine = (u == sk_viewer)
                        if mine:
                            me = {"sifa": bool(s.get("sifa")),
                                  "frozen_until": s.get("frozen_until", 0),
                                  "motor_until": s.get("motor_until", 0),
                                  "lat": s["lat"], "lon": s["lon"], "heading": s["heading"]}
                        ships.append({
                            "user": u,
                            "lat": s["lat"], "lon": s["lon"], "heading": s["heading"],
                            "mine": mine,
                            "revealed": now < s.get("motor_until", 0),
                        })
            if need_save:
                sifa_save_to_github()
            self._json_response(200, {"ships": ships, "area": area, "me": me, "logs": logs})
        elif url.path == "/walkerstate":
            chat_id = int(params.get("chat", ["0"])[0])
            viewer = params.get("user", [""])[0]
            viewer_name = params.get("name", [""])[0][:64]
            now = time.time()
            today = datetime.datetime.now(MSK_TZ).strftime("%Y-%m-%d")
            me = None
            others = []
            need_wsave = False
            need_gsave = False
            spawn_klad = None
            with walker_lock:
                walkers = walker_state.setdefault(chat_id, {})
                spawned = False
                arrived = False
                with geo_lock:
                    mkey = resolve_marker_key(chat_id, viewer, viewer_name)
                    if mkey is None:
                        self._json_response(403, {"error": "сначала поставь метку на карте"})
                        return
                    w = walkers.get(mkey)
                    if w is None:
                        w = _walker_spawn(viewer_name or mkey, viewer)
                        walkers[mkey] = w
                        marker = geo_state[chat_id][mkey]
                        if "food" not in marker:
                            marker["food"] = WALKER_START_FOOD
                            marker["food_day"] = today
                            marker["food_cooked"] = 0
                            need_gsave = True
                        need_wsave = True
                        spawned = True
                        logline(f"walker spawn chat={chat_id} user={mkey!r}")
                    if walker_progress(w):
                        need_wsave = True
                        arrived = True
                    marker = geo_state[chat_id].get(mkey) or {}
                    if marker.get("food_day") != today:
                        marker["food_day"] = today
                        marker["food_cooked"] = 0
                        need_gsave = True
                    me = {"lat": w["lat"], "lon": w["lon"],
                          "energy": round(w.get("energy", 0.0), 1),
                          "moving": bool(w.get("route")),
                          "food": marker.get("food", 0),
                          "cook_in": max(0, int(marker.get("food_ready_ts", 0.0) - now)),
                          "cooked_left": FOOD_DAILY_MAX - marker.get("food_cooked", 0)}
                    for u, o in walkers.items():
                        if u == mkey:
                            continue
                        if walker_progress(o):
                            need_wsave = True
                        others.append({"lat": o["lat"], "lon": o["lon"],
                                       "name": o.get("name", "?")})
                # geo_lock отпущен — порядок локов walker → klad → geo не нарушаем:
                # klad_ensure/klad_on_arrival сами берут klad_lock (и geo_lock внутри)
                if spawned:
                    # первый следопыт в чате — зарываем клад и анонсируем квест
                    spawn_klad = klad_ensure(chat_id)
                if arrived and klad_on_arrival(chat_id, mkey, w):
                    need_gsave = True
            if need_wsave:
                walker_save_to_github()
            if need_gsave:
                geo_save_to_github()
            if spawn_klad is not None:
                # анонс клада — вне всех локов
                try:
                    tg_send_message_id(chat_id, spawn_klad["hints"][0][1])
                except Exception as e:
                    print(f"[paint_bot] анонс клада не ушёл: {e!r}", flush=True)
            stations = [{"key": s["key"], "name": s["name"],
                         "lat": _walker_station_point(s)[0],
                         "lon": _walker_station_point(s)[1]} for s in WALKER_STATIONS]
            self._json_response(200, {"me": me, "others": others, "stations": stations})
        elif url.path == "/geodata":
            chat_id = int(params.get("chat", ["0"])[0])
            viewer = params.get("user", [""])[0]
            viewer_name = params.get("name", [""])[0][:64]
            # кто я на самом деле: сервер узнаёт по tid Telegram, а не по сырому ключу клиента
            me_key = resolve_marker_key(chat_id, viewer, viewer_name)
            with geo_lock:
                letters_out = []
                changed = False
                now = time.time()
                for lid, letter in list(letters_state.items()):
                    if letter["chat"] != chat_id:
                        continue
                    # прочитанное письмо можно перечитывать сутки, потом удаляется автоматически
                    # (непрочитанные и письма в пути НЕ удаляются — только уже прочитанные)
                    read_ts = letter.get("read_ts")
                    if (read_ts is not None
                            and now - read_ts > LETTER_READ_KEEP_SEC):
                        del letters_state[lid]
                        changed = True
                        continue
                    lat, lon, arrived = letter_progress(letter)
                    if arrived and not letter["arrived"]:
                        letter["arrived"] = True
                        dest = geo_state.get(chat_id, {}).get(letter["to"])
                        if dest is not None:
                            dest["got"] = dest.get("got", 0) + 1
                            dest_name = dest.get("name", letter["to"])
                        else:
                            dest_name = letter["to"]
                        changed = True
                        # уведомление адресату в чат Telegram (один раз, при доставке;
                        # читать письмо можно в течение часа — столько же живёт уведомление)
                        try:
                            tg_send_with_cleanup(
                                chat_id,
                                f"📬 {geo_mention(chat_id, letter['to'], dest_name)}! Тебе прибыло "
                                "письмо — открой карту чата и нажми на 📬, чтобы прочитать.",
                                ARRIVAL_NOTIFY_TTL_SEC,
                                html_mode=True,
                            )
                        except Exception as e:
                            print(f"[paint_bot] уведомление о письме не ушло: {e!r}", flush=True)
                    dest = geo_state.get(chat_id, {}).get(letter["to"])
                    letters_out.append({
                        "id": lid, "lat": round(lat, 6), "lon": round(lon, 6),
                        "arrived": arrived,
                        "read": letter.get("read_ts") is not None,
                        "mine": viewer_matches(letter["to"], viewer, viewer_name, chat_id),
                        "to": letter["to"],
                        "from_name": letter_sender_name(chat_id, letter),
                        "from": letter["from"],  # user key отправителя — для кнопки «Ответить»
                        "to_name": (dest or {}).get("name", "удалённой метке"),
                        "from_lat": letter["from_lat"], "from_lon": letter["from_lon"],
                        "to_lat": letter["to_lat"], "to_lon": letter["to_lon"],
                        # дата доставки (МСК) — для «старого письма» при чтении
                        "date": time.strftime("%d.%m.%Y %H:%M",
                                              time.gmtime((letter.get("arrived_ts")
                                                           or letter["start_ts"]) + 3 * 3600)),
                    })
                # прибывшие письма одного адресата лежат в точке его метки друг
                # на друге — клик достаётся только верхнему; разносим по кругу
                by_dest = {}
                for it in letters_out:
                    if it["arrived"]:
                        by_dest.setdefault(it["to"], []).append(it)
                for items in by_dest.values():
                    if len(items) < 2:
                        continue
                    base_lat, base_lon = items[0]["lat"], items[0]["lon"]
                    lat_cos = max(math.cos(math.radians(base_lat)), 0.3)
                    for i, it in enumerate(items):
                        ang = 2 * math.pi * i / len(items)
                        it["lat"] = round(base_lat + 0.003 * math.cos(ang), 6)
                        it["lon"] = round(base_lon + 0.003 * math.sin(ang) / lat_cos, 6)
                markers = [dict(m) for m in geo_state.get(chat_id, {}).values()]
                # непрочитанные письма по адресатам: для значка почтового ящика на метке
                # (письма в пути на ящик не влияют — только доставленные и непрочитанные)
                unread_by_to = {}
                for letter in letters_state.values():
                    if (letter["chat"] == chat_id and letter.get("arrived")
                            and letter.get("read_ts") is None):
                        unread_by_to[letter["to"]] = unread_by_to.get(letter["to"], 0) + 1
                for m in markers:
                    m["unread"] = unread_by_to.get(m["user"], 0)
                # ---------- Ванильный Вулкан ----------
                # ---------- Корабли (Галеоны) ----------
                ships_out = []
                duel_out = None
                now = time.time()
                duel_cleanup(now)
                chat_ships = [(k, s) for k, s in ships_state.items()
                              if s.get("chat") == chat_id]
                for key, sh in chat_ships:
                    if ship_progress(sh):
                        changed = True
                for key, sh in chat_ships:
                    mine = viewer_matches(sh["user"], viewer, viewer_name, chat_id)
                    boarding = False
                    if not sh.get("sunk"):
                        for key2, sh2 in chat_ships:
                            if key2 == key or sh2.get("sunk"):
                                continue
                            if haversine_km(sh["lat"], sh["lon"],
                                            sh2["lat"], sh2["lon"]) <= SHIP_BOARD_KM:
                                boarding = True
                                break
                    d = ship_in_duel(chat_id, sh["user"])
                    if mine:
                        dv = duel_view_for(chat_id, sh["user"], now)
                        if dv is not None:
                            duel_out = public_duel(dv, sh["user"])
                    ships_out.append({
                        "id": key,
                        "user": sh["user"], "name": sh.get("name", ""),
                        "lat": round(sh["lat"], 6), "lon": round(sh["lon"], 6),
                        "sunk": bool(sh.get("sunk")), "moving": sh.get("to_lat") is not None,
                        "mine": mine, "boarding": boarding, "in_duel": d is not None,
                        "wins": sh.get("wins", 0),
                        "built": (geo_state.get(chat_id, {}).get(sh["user"]) or {}).get("ships_built", 0),
                        "lost": (geo_state.get(chat_id, {}).get(sh["user"]) or {}).get("ships_lost", 0),
                        # параметры маршрута для плавной клиентской интерполяции
                        "nav_from_lat": sh.get("nav_from_lat"), "nav_from_lon": sh.get("nav_from_lon"),
                        "to_lat": sh.get("to_lat"), "to_lon": sh.get("to_lon"),
                        "route": sh.get("route") if sh.get("to_lat") is not None else None,
                        "nav_ts": sh.get("nav_ts"),
                    })
                # активные абордажи — точки «сражения» между сцепленными кораблями
                battles_out = []
                seen_duels = set()
                for key, sh in chat_ships:
                    bd = ship_in_duel(chat_id, sh["user"])
                    if bd is None or bd["id"] in seen_duels:
                        continue
                    seen_duels.add(bd["id"])
                    duel_tick(bd, now)
                    if ship_in_duel(chat_id, sh["user"]) is None:
                        continue   # дуэль отменилась по таймауту ожидания
                    sa = ships_state.get(ship_key(chat_id, bd["a"]))
                    sb = ships_state.get(ship_key(chat_id, bd["b"]))
                    if sa is None or sb is None:
                        continue
                    ba_name, bb_name = duel_display_names(bd)
                    battles_out.append({
                        "id": bd["id"],
                        "lat": round((sa["lat"] + sb["lat"]) / 2, 6),
                        "lon": round((sa["lon"] + sb["lon"]) / 2, 6),
                        "a": ba_name, "b": bb_name,
                    })
                if changed:
                    ships_save_to_github()
                # мемориальные рифы: показываем всем, в боях не участвуют
                for wkey, wr in wrecks_state.items():
                    if wr.get("chat") != chat_id:
                        continue
                    ships_out.append({
                        "id": "wreck:" + wkey,
                        "user": wr.get("user", wkey), "name": wr.get("name", ""),
                        "lat": round(wr["lat"], 6), "lon": round(wr["lon"], 6),
                        "sunk": True, "moving": False,
                        "mine": viewer_matches(wr.get("user", ""), viewer, viewer_name, chat_id),
                        "boarding": False, "in_duel": False, "wins": wr.get("wins", 0),
                        "built": (geo_state.get(chat_id, {}).get(wr.get("user", "")) or {}).get("ships_built", 0),
                        "lost": (geo_state.get(chat_id, {}).get(wr.get("user", "")) or {}).get("ships_lost", 0),
                    })
                # ---------- Ванильный Вулкан ----------
                v, _spawned_now = volcano_get_active(chat_id)
                volcano_out = None
                if v is not None:
                    remain = max(0, int(VOLCANO_LIFETIME_SEC - (time.time() - v["spawn_ts"])))
                    volcano_out = {"lat": v["lat"], "lon": v["lon"],
                                   "used": v["used"], "remain_sec": remain}
                # ---------- Метеорит: свежая воронка + все старые ----------
                meteors_out = []
                m = meteor_state.get(chat_id)
                if m is not None:
                    for c in m.get("craters", []):
                        meteors_out.append({"lat": c["lat"], "lon": c["lon"],
                                            "zp": c.get("zp", 0), "fresh": False})
                    cur = m.get("current")
                    if cur is not None and time.time() - cur["fall_ts"] < METEOR_LIFETIME_SEC:
                        meteors_out.append({"lat": cur["lat"], "lon": cur["lon"],
                                            "zp": 0 if cur["taken"] else 1, "fresh": True})
                # ---------- Розовые какашки: позиции и прибытия ----------
                poops_out = []
                for pid, poop in list(poops_state.items()):
                    if poop["chat"] != chat_id:
                        continue
                    plat, plon, parrived = poop_progress(poop)
                    if parrived and not poop["arrived"]:
                        poop["arrived"] = True
                        poop["arrived_ts"] = now
                        dest = geo_state.get(chat_id, {}).get(poop["to"])
                        if dest is not None:
                            dest["poops"] = dest.get("poops", 0) + 1
                            dest_name = dest.get("name", poop["to"])
                        else:
                            dest_name = poop["to"]
                        changed = True
                        # уведомление адресату в чат (один раз, при доставке); отправитель анонимен;
                        # какашка исчезает с карты через 5 минут — уведомление живёт час
                        try:
                            tg_send_with_cleanup(
                                chat_id,
                                f"🌋 Ванильный Вулкан извергся! К тебе, "
                                f"{geo_mention(chat_id, poop['to'], dest_name)}, прилетела "
                                "Розовая Какашка 💩🩷. Примирительно улыбнись и неси в дом — "
                                "принесёт удачу! 😄😊",
                                ARRIVAL_NOTIFY_TTL_SEC,
                                html_mode=True,
                            )
                        except Exception as e:
                            print(f"[paint_bot] уведомление о какашке не ушло: {e!r}", flush=True)
                    if parrived:
                        # прибывшая какашка исчезает через 5 минут (счётчик адресата уже увеличен)
                        arrived_ts = poop.get("arrived_ts")
                        if arrived_ts is None:  # старые записи без метки времени
                            poop["arrived_ts"] = now
                        elif now - arrived_ts > POOP_ARRIVED_TTL_SEC:
                            del poops_state[pid]
                            changed = True
                            continue
                    poops_out.append({
                        "id": pid, "lat": round(plat, 6), "lon": round(plon, 6),
                        "arrived": parrived,
                        "mine": viewer_matches(poop["to"], viewer, viewer_name, chat_id),
                        "to_name": poop.get("to_name", ""),
                        "i_sent": viewer_matches(poop.get("from", ""), viewer, viewer_name, chat_id),
                        "from_lat": poop["from_lat"], "from_lon": poop["from_lon"],
                        "to_lat": poop["to_lat"], "to_lon": poop["to_lon"],
                    })
                # ---------- Похотливый Кит: активный кит ----------
                s, _sub_spawned = submarine_get_active(chat_id)
                submarine_out = None
                if s is not None:
                    remain = max(0, int(SUBMARINE_LIFETIME_SEC - (time.time() - s["spawn_ts"])))
                    submarine_out = {"lat": s["lat"], "lon": s["lon"],
                                     "used": s["used"], "remain_sec": remain}
                # ---------- Подарки с подводной лодки ----------
                gifts_out = []
                for gid, gift in list(gifts_state.items()):
                    if gift["chat"] != chat_id:
                        continue
                    glat, glon, garrived = gift_progress(gift)
                    if garrived and not gift["arrived"]:
                        gift["arrived"] = True
                        gift["arrived_ts"] = now
                        dest = geo_state.get(chat_id, {}).get(gift["to"])
                        dest_name = (dest or {}).get("name", gift["to"])
                        changed = True
                        # уведомление адресату в чат (один раз, при доставке);
                        # автоудаление через 10 минут (по требованию владельца)
                        try:
                            tg_send_with_cleanup(
                                chat_id,
                                f"🎁 {geo_mention(chat_id, gift['to'], dest_name)}! Похотливый Кит "
                                f"прислал тебе подарок — беги открывай! Он уже ждёт у твоей метки 😏🐳",
                                600,
                                html_mode=True,
                            )
                        except Exception as e:
                            print(f"[paint_bot] уведомление о подарке не ушло: {e!r}", flush=True)
                    if gift["arrived"] and gift.get("opened"):
                        continue  # открытый подарок живёт в инфо адресата, маркер снят
                    gifts_out.append({
                        "id": gid, "lat": round(glat, 6), "lon": round(glon, 6),
                        "arrived": garrived,
                        "mine": viewer_matches(gift["to"], viewer, viewer_name, chat_id),
                        "to": gift["to"],
                        "to_name": gift.get("to_name", ""),
                        "i_sent": viewer_matches(gift.get("from", ""), viewer, viewer_name, chat_id),
                        "from_lat": gift["from_lat"], "from_lon": gift["from_lon"],
                        "to_lat": gift["to_lat"], "to_lon": gift["to_lon"],
                    })
                # прибывшие подарки одного адресата не должны ложиться друг на друга
                by_gdest = {}
                for it in gifts_out:
                    if it["arrived"]:
                        by_gdest.setdefault(it["to"], []).append(it)
                for items in by_gdest.values():
                    if len(items) < 2:
                        continue
                    base_lat, base_lon = items[0]["lat"], items[0]["lon"]
                    lat_cos = max(math.cos(math.radians(base_lat)), 0.3)
                    for i, it in enumerate(items):
                        ang = 2 * math.pi * i / len(items)
                        it["lat"] = round(base_lat + 0.003 * math.cos(ang), 6)
                        it["lon"] = round(base_lon + 0.003 * math.sin(ang) / lat_cos, 6)
                # открытые подарки — картинки в карточке метки-адресата (видят все)
                pics_by_to = {}
                for gift in gifts_state.values():
                    if (gift["chat"] == chat_id and gift.get("opened")
                            and gift.get("picture")):
                        pics_by_to.setdefault(gift["to"], []).append(gift["picture"])
                for m in markers:
                    pics = pics_by_to.get(m["user"])
                    if pics:
                        m["gift_pics"] = pics
                # ---------- Острова: перелёты гостей, награды, позиции ----------
                islands_out = []
                planes_out = []
                for ikey, isl in list(islands_state.items()):
                    if isl["chat"] != chat_id or isl.get("banned"):
                        continue
                    g = isl.get("guest")
                    if g and g["leg"] in ("to_guest", "to_island", "home"):
                        plat, plon, parrived = island_plane_progress(g)
                        if parrived:
                            changed = True
                            if g["leg"] == "to_guest":
                                # самолёт долетел ЗА гостем — теперь везёт его на остров
                                g["leg"] = "to_island"
                                g["from_lat"], g["from_lon"] = g["to_lat"], g["to_lon"]
                                g["to_lat"], g["to_lon"] = isl["lat"], isl["lon"]
                                g["start_ts"] = now
                                try:
                                    tg_send_with_cleanup(
                                        chat_id,
                                        f"✈️ {geo_mention(chat_id, g['user'], g['name'])}! За тобой "
                                        f"прилетел самолёт с острова «{isl['name']}» — тебя зовут "
                                        "в гости! 🏝️😎 Готовь плавки, скоро приземлишься!",
                                        ARRIVAL_NOTIFY_TTL_SEC,
                                        html_mode=True,
                                    )
                                except Exception as e:
                                    print(f"[paint_bot] уведомление гостю не ушло: {e!r}", flush=True)
                            elif g["leg"] == "to_island":
                                # гость на острове: награды гостю + опыт острову
                                g["leg"] = "staying"
                                g["staying_ts"] = time.time()
                                isl["visits"] = isl.get("visits", 0) + 1
                                isl["xp"] = isl.get("xp", 0) + 1
                                zp_reward = 2 if "bar" in isl.get("buildings", []) else 1
                                stardust_earn(chat_id, g["user"], zp_reward)
                                g["souvenir"] = random.choice(SOUVENIR_PICS)
                                gmarker = geo_state.get(chat_id, {}).get(g["user"])
                                if gmarker is not None:
                                    gmarker.setdefault("souvenirs", []).append(g["souvenir"])
                                try:
                                    tg_send_with_cleanup(
                                        chat_id,
                                        f"🏝️ {geo_mention(chat_id, g['user'], g['name'])} приземлился "
                                        f"на «{isl['name']}»!\n"
                                        f"Гостю: +{zp_reward} ЗП и сувенир {g['souvenir']} 🎁 "
                                        "Когда нагуляешься — жми «Улететь», а до этого не забудь "
                                        "оставить послание на скале 🪨✎\n"
                                        "Владельцам острова: +1 опыт 😎",
                                        ARRIVAL_NOTIFY_TTL_SEC,
                                        html_mode=True,
                                    )
                                except Exception as e:
                                    print(f"[paint_bot] уведомление о госте не ушло: {e!r}", flush=True)
                            else:  # home — гость улетел домой, сессия закрыта
                                gname = g["name"]
                                guser = g["user"]
                                isl["guest"] = None
                                try:
                                    tg_send_with_cleanup(
                                        chat_id,
                                        f"✈️ {geo_mention(chat_id, guser, gname)} улетел с острова "
                                        f"«{isl['name']}» домой. Возвращайся, здесь тепло 🙂",
                                        ARRIVAL_NOTIFY_TTL_SEC,
                                        html_mode=True,
                                    )
                                except Exception as e:
                                    print(f"[paint_bot] уведомление об отлёте не ушло: {e!r}", flush=True)
                        else:
                            planes_out.append({
                                "island": isl["owner"], "guest_name": g["name"],
                                "leg": g["leg"], "lat": round(plat, 6), "lon": round(plon, 6),
                                "from_lat": g["from_lat"], "from_lon": g["from_lon"],
                                "to_lat": g["to_lat"], "to_lon": g["to_lon"],
                            })
                    cur_guest = isl.get("guest")
                    # ШТОРМ: ленивое расписание — раз ~в 2 часа, в случайный момент окна
                    _storm = isl.get("storm")
                    if _storm and now >= _storm.get("active_until", 0):
                        isl["storm"] = None
                        _storm = None
                        changed = True
                    if not isl.get("next_storm_ts"):
                        isl["next_storm_ts"] = now + random.uniform(1800, ISLAND_STORM_PERIOD_SEC)
                        changed = True
                    elif _storm is None and now >= isl["next_storm_ts"]:
                        isl["storm"] = {"active_until": now + ISLAND_STORM_LIVE_SEC,
                                        "collected": []}
                        isl["next_storm_ts"] = now + random.uniform(5400, 9000)
                        _storm = isl["storm"]
                        changed = True
                        try:
                            tg_send_with_cleanup(
                                chat_id,
                                f"🌩 Шторм пронёсся над «{isl['name']}»! На берег выбросило "
                                f"брёвна — у тебя 15 минут. Жми «Собрать дерево» "
                                f"в Действиях острова 🌲",
                                ARRIVAL_NOTIFY_TTL_SEC,
                            )
                        except Exception as e:
                            print(f"[paint_bot] уведомление о шторме не ушло: {e!r}", flush=True)
                    storm_left = (_storm["active_until"] - now) if _storm else 0
                    _collected = (_storm or {}).get("collected") or []
                    _vmkey = resolve_marker_key(chat_id, viewer, viewer_name)
                    _storm_collected = bool(_collected and
                                            (viewer in _collected
                                             or (_vmkey and _vmkey in _collected)))
                    owners = isl.get("owners") or [isl["owner"]]
                    onames = []
                    for ow in owners:
                        om = geo_state.get(chat_id, {}).get(ow)
                        onames.append((om or {}).get("name", ow))
                    islands_out.append({
                        "owner": isl["owner"],
                        "owner_name": " и ".join(onames) or isl.get("owner_name", "?"),
                        "owners": owners,
                        "name": isl["name"], "lat": isl["lat"], "lon": isl["lon"],
                        "level": island_level(isl), "xp": isl.get("xp", 0),
                        "visits": isl.get("visits", 0),
                        "buildings": isl.get("buildings", []),
                        "guest": (None if cur_guest is None
                                  else {"name": cur_guest["name"], "leg": cur_guest["leg"],
                                        "user": cur_guest["user"],
                                        "staying_ts": cur_guest.get("staying_ts", 0)}),
                        "poop_today": (isl.get("poop_today", 0)
                                       if isl.get("poop_day") == datetime.datetime.now(
                                           MSK_TZ).strftime("%Y-%m-%d") else 0),
                        "storm_left": max(0, int(storm_left)),
                        "storm_collected": _storm_collected,
                        "mine": any(viewer_matches(o, viewer, viewer_name, chat_id)
                                    for o in owners),
                    })
                # сувениры гостей — в карточки их меток (видят все) + баланс ЗП каждой метки
                for m in markers:
                    src = geo_state.get(chat_id, {}).get(m["user"])
                    if src and src.get("souvenirs"):
                        m["souvenirs"] = src["souvenirs"]
                    m["zp"] = stardust_balance(chat_id, m["user"])
                # ---------- Морской Рынок: владелец, отсчёт владения, мешок зрителя ----------
                mk_entry = market_state.get(str(chat_id))
                if mk_entry is None:
                    mk_entry = market_state.get(chat_id)
                market_out = {"lat": MARKET_LAT, "lon": MARKET_LON,
                              "owner": None, "owner_name": None, "mine": False,
                              "hold_sec": 0, "gifts": 0}
                if mk_entry and mk_entry.get("owner"):
                    owner_key = mk_entry["owner"]
                    market_out["owner"] = owner_key
                    market_out["owner_name"] = mk_entry.get("owner_name") or "?"
                    market_out["mine"] = viewer_matches(owner_key, viewer, viewer_name, chat_id)
                    market_out["hold_sec"] = max(
                        0, int(now - mk_entry.get("captured_ts", now)))
                market_out["gifts"] = len([
                    g for g in gifts_state.values()
                    if g["chat"] == chat_id and g.get("opened") and g.get("picture")
                    and viewer_matches(g["to"], viewer, viewer_name, chat_id)])
            if changed:
                geo_save_to_github()
                letters_save_to_github()
                volcano_save_to_github()
                submarine_save_to_github()
                islands_save_to_github()
                meteor_save_to_github()
            self._respond(
                200,
                json.dumps({"markers": markers, "letters": letters_out,
                            "volcano": volcano_out, "poops": poops_out,
                            "meteors": meteors_out, "stardust": stardust_balance(chat_id, viewer, viewer_name),
                            "submarine": submarine_out, "gifts": gifts_out,
                            "islands": islands_out, "planes": planes_out,
                            "ships": ships_out, "ship_duel": duel_out,
                            "ship_battles": battles_out,
                            "market": market_out,
                            "me": me_key,
                            "viewer_admin": tg_chat_admin_allowed(
                                chat_id, self.headers.get("X-TG-Init-Data", ""))},
                           ensure_ascii=False).encode("utf-8"),
                "application/json; charset=utf-8",
            )
        elif url.path in ("/begin", "/end"):
            # мягкая очередь: отметить, что кто-то открыл/закрыл холст
            chat_id = int(params.get("chat", ["0"])[0])
            user = params.get("user", ["Аноним"])[0][:32] or "Аноним"
            state = paint_state.get(chat_id)
            if state is not None:
                if url.path == "/begin":
                    state["drawer"] = user
                    state["lock_time"] = time.time()
                    state["last_activity"] = time.time()
                    paint_update_queue.put(chat_id)
                elif state.get("drawer") == user:
                    # освобождает только тот, кто успел занять (или замок уже чужой)
                    state["drawer"] = None
                    paint_update_queue.put(chat_id)
            self._respond(200, b"ok")
        else:
            self._respond(404, b"not found")

    def do_POST(self):
        init_data = self.headers.get("X-TG-Init-Data", "")
        # каждое действие — только из Telegram: проверяем подпись WebApp (initData)
        if not tg_init_data_valid(init_data):
            self._json_response(403, {"error": "только из Telegram"})
            return
        url = urlparse(self.path)
        # тело читаем один раз здесь; хендлеры получат его через подменённый rfile
        length = int(self.headers.get("Content-Length") or 0)
        raw = self.rfile.read(length) if length else b""
        self.rfile = io.BytesIO(raw)
        # полный функционал — только админам группы этого чата
        try:
            body = json.loads(raw.decode("utf-8")) if raw else {}
        except Exception:
            body = {}
        try:
            chat_id = int(body.get("chat") or parse_qs(url.query).get("chat", ["0"])[0])
        except Exception:
            chat_id = 0
        if not tg_chat_admin_allowed(chat_id, init_data):
            self._json_response(403, {"error": "играть могут только админы этой группы 🤷"})
            return
        if url.path in ("/geomark", "/geodel", "/geoicon"):
            self._handle_geo_post(url)
            return
        if url.path in ("/geosend", "/georead"):
            self._handle_letter_post(url)
            return
        if url.path == "/sifamove":
            self._handle_sifa_move_post()
            return
        if url.path == "/sifaspawn":
            self._handle_sifa_spawn_post()
            return
        if url.path == "/sifaarea":
            self._handle_sifa_area_post()
            return
        if url.path == "/sifamotor":
            self._handle_sifa_motor_post()
            return
        if url.path == "/sifaexit":
            self._handle_sifa_exit_post()
            return
        if url.path == "/walkermove":
            self._handle_walker_move_post()
            return
        if url.path == "/walkerfood":
            self._handle_walker_food_post()
            return
        if url.path == "/walkerstation":
            self._handle_walker_station_post()
            return
        if url.path == "/volcano":
            self._handle_volcano_post(url)
            return
        if url.path == "/meteor":
            self._handle_meteor_post(url)
            return
        if url.path == "/letterboost":
            self._handle_letter_boost_post(url)
            return
        if url.path == "/spawnevent":
            self._handle_spawnevent_post(url)
            return
        if url.path == "/subgift":
            self._handle_subgift_post(url)
            return
        if url.path == "/subopen":
            self._handle_subopen_post(url)
            return
        if url.path in ("/islandbuy", "/islandinvite", "/islandleave",
                        "/islandbuild", "/islandpoop", "/islanddel", "/islandrock",
                        "/islandstorm", "/islandkick",
                        "/shipbuild", "/shipnav", "/shipboard", "/shipready", "/shippick",
                        "/shipduelseen"):
            self._handle_island_post(url)
            return
        if url.path in ("/marketcapture", "/marketexchange"):
            self._handle_market_post(url)
            return
        if url.path != "/save":
            self._respond(404, b"not found")
            return
        params = parse_qs(url.query)
        chat_id = int(params.get("chat", ["0"])[0])
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            data_url = payload["img"]
            png_bytes = io.BytesIO(base64.b64decode(data_url.split(",", 1)[1])).getvalue()
        except Exception:
            self._respond(400, b"bad request")
            return
        state = paint_state.setdefault(chat_id, new_paint_state())
        state["image"] = png_bytes
        state["dirty_img"] = True
        state["drawer"] = None  # рисунок отправлен — холст свободен
        state["last_activity"] = time.time()
        paint_update_queue.put(chat_id)
        self._respond(200, b"ok")

    def _handle_geo_post(self, url):
        """Поставить (/geomark) или удалить (/geodel) метку на карте чата."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
        except Exception:
            self._respond(400, b"bad request")
            return
        if not user:
            self._respond(400, b"bad request")
            return
        if url.path == "/geomark":
            try:
                name = (str(payload.get("name"))[:32] or "Аноним").strip() or "Аноним"
                icon = str(payload.get("icon", "📍"))[:8] or "📍"
                lat = float(payload["lat"])
                lon = float(payload["lon"])
            except Exception:
                self._respond(400, b"bad request")
                return
            if not (-90 <= lat <= 90 and -180 <= lon <= 180):
                self._respond(400, b"bad coords")
                return
            with geo_lock:
                chat_markers = geo_state.setdefault(chat_id, {})
                old = chat_markers.get(user, {})
                # новым меткам сразу ставим tid (ключ = id Telegram) и сохраняем
                # накопленное (какашки, дерево, сувениры, статистика кораблей) —
                # иначе повторная постановка метки всё обнуляла
                tid = old.get("tid") or (str(user) if str(user).isdigit() else None)
                chat_markers[user] = {
                    "user": user, "name": name, "icon": icon,
                    "lat": round(lat, 6), "lon": round(lon, 6),
                    "got": old.get("got", 0), "read": old.get("read", 0),
                    "poops": old.get("poops", 0), "wood": old.get("wood", 0),
                    "souvenirs": old.get("souvenirs", []),
                    "ships_built": old.get("ships_built", 0),
                    "ships_lost": old.get("ships_lost", 0),
                    "tid": tid,
                }
            geo_save_to_github()
            self._respond(200, b"ok")
        elif url.path == "/geoicon":
            icon = str(payload.get("icon", ""))[:8]
            with geo_lock:
                mkey = resolve_marker_key(chat_id, user, str(payload.get("name", ""))[:64])
                marker = geo_state.get(chat_id, {}).get(mkey) if mkey else None
                if marker is None:
                    self._json_response(404, {"error": "метки нет"})
                    return
                marker["icon"] = icon or "📍"
                geo_save_to_github()
            self._json_response(200, {"ok": True})
        else:  # /geodel
            removed = False
            with geo_lock:
                markers = geo_state.get(chat_id)
                if markers and user in markers:
                    del markers[user]
                    removed = True
                # письма, шедшие к удалённой метке, тоже удаляются (удаление отключено — LETTERS_NEVER_DELETE)
                doomed = ([] if LETTERS_NEVER_DELETE
                          else [lid for lid, l in letters_state.items()
                                if l["chat"] == chat_id and l["to"] == user])
                for lid in doomed:
                    del letters_state[lid]
            if removed:
                geo_save_to_github()
            if doomed:
                letters_save_to_github()
            self._respond(200, b"ok")

    def _json_response(self, code: int, obj: dict) -> None:
        self._respond(code, json.dumps(obj, ensure_ascii=False).encode("utf-8"),
                      "application/json; charset=utf-8")

    def _handle_letter_post(self, url):
        """Отправить (/geosend) или прочитать (/georead) письмо."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if url.path == "/geosend":
            to_user = str(payload.get("to_user", ""))[:64]
            name = (str(payload.get("name"))[:32]).strip() or "Аноним"
            text = str(payload.get("text", "")).strip()
            if not user or not to_user or user == to_user or not text:
                self._json_response(400, {"error": "bad request"})
                return
            if len(text) > LETTER_MAX_TEXT:
                self._json_response(400, {"error": f"слишком длинное (максимум {LETTER_MAX_TEXT})"})
                return
            with geo_lock:
                markers = geo_state.get(chat_id, {})
                # мягкий матчинг: ключ метки может быть именем (браузер) или числовым id (TG)
                frm_key = resolve_marker_key(chat_id, user, name)
                frm = markers.get(frm_key) if frm_key else None
                to_key = to_user if to_user in markers else resolve_marker_key(chat_id, to_user, "")
                to = markers.get(to_key) if to_key else None
                if frm is None or to is None or frm_key == to_key:
                    self._json_response(404, {"error": "нет метки у отправителя или адресата"})
                    return
                # гость на острове не принимает почту
                if island_guest_at(chat_id, to_key) is not None:
                    self._json_response(409, {"error": "Адресат в отъезде."})
                    return
                # блокирует отправку только письмо, реально летящее к этому адресату;
                # доставленные/прочитанные не мешают (а удаление писем отключено — иначе
                # первая же доставка вечно блокировала бы пару)
                matched = 0
                for letter in letters_state.values():
                    if letter["chat"] != chat_id or letter["from"] != frm_key or letter["to"] != to_key:
                        continue
                    matched += 1
                    # диагностика: считаем встроенной математикой и логируем сырые данные
                    _now = time.time()
                    _start = letter["start_ts"]
                    _sp = letter_speed_km_per_min(letter)
                    _tot = haversine_km(letter["from_lat"], letter["from_lon"],
                                        letter["to_lat"], letter["to_lon"])
                    try:
                        _elapsed = (_now - _start) / 60.0
                        _live = (_tot <= 0) or (_elapsed * _sp >= _tot)
                    except Exception as _e:
                        _elapsed, _live = f"ERR {_e!r}", None
                    logline(f"check /geosend user={user!r} to={to_user!r} lid={letter['id']} "
                            f"start_type={type(_start).__name__} start={_start!r} now={_now:.0f} "
                            f"elapsed_min={_elapsed!r} speed={_sp} total_km={_tot:.1f} live={_live} "
                            f"lp_firstline={letter_progress.__code__.co_firstlineno}")
                    _, _, arrived_flag = letter_progress(letter)
                    if not arrived_flag:  # письмо реально ещё летит — только это блокирует пару
                        logline(f"409 /geosend user={user!r} to={to_user!r} lid={letter['id']} still_flying")
                        self._json_response(409, {"error": "уже есть письмо в пути этому адресату (lid=" + letter["id"] + ")"})
                        return
                logline(f"check /geosend pass user={user!r} to={to_user!r} matching={matched}")
                lid = uuid.uuid4().hex[:10]
                total = haversine_km(frm["lat"], frm["lon"], to["lat"], to["lon"])
                letters_state[lid] = {
                    "id": lid, "chat": chat_id, "from": frm_key, "from_name": name,
                    "to": to_key, "text": text,
                    "from_lat": frm["lat"], "from_lon": frm["lon"],
                    "to_lat": to["lat"], "to_lon": to["lon"],
                    "start_ts": time.time(), "arrived": False,
                }
            try:
                saved = letters_save_to_github()
                logline(f"200 /geosend user={user!r} to={to_user!r} chat={chat_id} id={lid} saved={saved}")
                fast_mult = LETTER_FAST_SENDERS.get(user) or LETTER_FAST_SENDERS.get(to_user)
                speed = (LETTER_SPEED_KM_PER_MIN * fast_mult if fast_mult else
                         LETTER_TEST_SPEED_KM_PER_MIN
                         if frozenset((user, to_user)) in LETTER_TEST_PAIRS
                         else LETTER_SPEED_KM_PER_MIN)
                eta = int(total / speed) + 1
                self._json_response(200, {"eta_min": eta})
            except Exception as e:
                logline(f"ERROR /geosend after insert user={user!r} to={to_user!r}: {e!r}")
                try:
                    self._json_response(500, {"error": "внутренняя ошибка, попробуй ещё раз"})
                except Exception:
                    pass
            return
        # /georead
        lid = str(payload.get("id", ""))[:16]
        with geo_lock:
            letter = letters_state.get(lid)
            if letter is None or letter["chat"] != chat_id:
                self._json_response(404, {"error": "письмо не найдено"})
                return
            if not viewer_matches(letter["to"], user,
                                  str(payload.get("name", ""))[:64], chat_id):
                self._json_response(403, {"error": "это письмо не тебе"})
                return
            _, _, arrived = letter_progress(letter)
            if not arrived:
                self._json_response(409, {"error": "письмо ещё в пути"})
                return
            now = time.time()
            read_ts = letter.get("read_ts")
            if read_ts is not None and now - read_ts > LETTER_READ_KEEP_SEC:
                del letters_state[lid]
                expired = True
            else:
                expired = False
            if not expired:
                if read_ts is None:
                    # первое чтение: фиксируем время и счётчик «прочитано»
                    letter["read_ts"] = now
                    dest = geo_state.get(chat_id, {}).get(letter["to"])
                    if dest is not None:
                        dest["read"] = dest.get("read", 0) + 1
                result = {
                    "from": letter_sender_name(chat_id, letter),
                    "from_id": letter["from"],  # user key отправителя — для кнопки «Ответить»
                    "text": letter["text"],
                    "re_read": read_ts is not None,
                    "date": time.strftime("%d.%m.%Y %H:%M",
                                          time.gmtime((letter.get("arrived_ts")
                                                       or letter["start_ts"]) + 3 * 3600)),
                }
        if expired:
            geo_save_to_github()
            letters_save_to_github()
            self._json_response(404, {"error": "письмо удалено: срок перечитывания (сутки) истёк"})
            return
        geo_save_to_github()
        letters_save_to_github()
        self._json_response(200, result)

    def _handle_sifa_spawn_post(self) -> None:
        """СИФА: создать кораблик (один на игрока, спавн только в открытой воде)."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        import random as _rnd
        with sifa_lock:
            entry = _sifa_entry(chat_id)
            ships = entry["ships"]
            name = (str(payload.get("name", ""))[:32]).strip() or user
            sk = resolve_ship_key(ships, user, name)
            if sk is None:
                lat, lon = sifa_random_water(entry.get("area"))
                ship = {"lat": lat, "lon": lon, "heading": 0, "ts": time.time(),
                        "name": name, "sifa": False, "frozen_until": 0, "motor_until": 0}
                if str(user).isdigit():
                    ship["tid"] = user
                ships[user] = ship
            else:
                ship = ships[sk]
            if ships and not any(s.get("sifa") for s in ships.values()):
                _sifa_grant(entry, ships, _rnd.choice(list(ships)))
            _sifa_note_holder(entry, ships, time.time())
        sifa_save_to_github()
        self._json_response(200, {"ok": True, "lat": ship["lat"], "lon": ship["lon"],
                                  "sifa": bool(ship.get("sifa"))})

    def _handle_sifa_move_post(self) -> None:
        """СИФА: новая позиция корабля + передача Сифы по близости."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
            lat = float(payload["lat"])
            lon = float(payload["lon"])
            heading = float(payload.get("heading", 0))
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if not (-85.0 <= lat <= 85.0 and -180.0 <= lon <= 180.0):
            self._json_response(400, {"error": "координаты за пределами карты"})
            return
        name = str(payload.get("name", ""))[:64]
        now = time.time()
        teleported = False
        wood_picked = 0
        with sifa_lock:
            entry = _sifa_entry(chat_id)
            ships = entry["ships"]
            sk = resolve_ship_key(ships, user, name)
            ship = ships.get(sk) if sk else None
            if ship is None:
                self._json_response(404, {"error": "касатки ещё нет — нажми 🐬 в панели"})
                return
            if now < ship.get("frozen_until", 0):
                self._json_response(403, {"error": "ты неподвижен — только что принял Сифу",
                                          "frozen_until": ship["frozen_until"]})
                return
            jump = haversine_km(ship["lat"], ship["lon"], lat, lon)
            if jump > SIFA_MAX_JUMP_KM:
                self._json_response(409, {"error": "слишком резкий скачок"})
                return
            if sifa_is_land(lat, lon):
                self._json_response(422, {"error": "кораблик не плавает по суше"})
                return
            area = entry.get("area")
            if area and not sifa_area_ok(area, lat, lon):
                self._json_response(422, {"error": "за границами игры «Сифа»"})
                return
            ship.update({"lat": lat, "lon": lon, "heading": heading, "ts": now})
            # брёвна: подплыл вплотную — забираем (максимум 3 за ход)
            logs = entry.get("logs")
            if logs:
                keep = []
                for lg in logs:
                    if (wood_picked < 3
                            and haversine_km(lat, lon, lg["lat"], lg["lon"]) <= SIFA_LOG_PICK_KM):
                        wood_picked += 1
                    else:
                        keep.append(lg)
                if wood_picked:
                    entry["logs"] = keep
            if ship.get("sifa"):
                for ou, os in ships.items():
                    if ou == sk or os.get("sifa"):
                        continue
                    if now < os.get("frozen_until", 0):
                        continue
                    if haversine_km(lat, lon, os["lat"], os["lon"]) <= SIFA_PASS_KM:
                        _sifa_grant(entry, ships, ou)
                        os["frozen_until"] = now + SIFA_FROZEN_SEC
                        ship["sifa"] = False
                        tlat, tlon = sifa_random_water(area)
                        ship.update({"lat": tlat, "lon": tlon, "ts": now})
                        # моторV8 гасится: Сифа передана, красный треугольник больше не нужен
                        ship["motor_until"] = 0
                        teleported = True
                        break
            if ships and not any(s.get("sifa") for s in ships.values()):
                import random as _rnd
                _sifa_grant(entry, ships, _rnd.choice(list(ships)))
            _sifa_note_holder(entry, ships, now)
        wood_total = 0
        if wood_picked:
            with geo_lock:
                mk = resolve_marker_key(chat_id, user, name)
                if mk is not None:
                    marker = geo_state[chat_id][mk]
                    marker["wood"] = marker.get("wood", 0) + wood_picked
                    wood_total = marker["wood"]
                    geo_save_to_github()
        sifa_save_to_github()
        self._json_response(200, {"ok": True, "teleported": teleported,
                                  "lat": ship["lat"], "lon": ship["lon"],
                                  "wood_got": wood_picked, "wood": wood_total})

    def _handle_sifa_area_post(self) -> None:
        """СИФА: Sumai задаёт границы области игры (4 угла по карте)."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
            points = payload["points"]
            assert len(points) == 4
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if user not in SIFA_AREA_ADMINS:
            self._json_response(403, {"error": "границы игры задаёт только Sumai"})
            return
        lats = [float(p[0]) for p in points]
        lons = [float(p[1]) for p in points]
        with sifa_lock:
            entry = _sifa_entry(chat_id)
            entry["area"] = [min(lats), min(lons), max(lats), max(lons)]
        sifa_save_to_github(force=True)
        self._json_response(200, {"ok": True, "area": entry["area"]})

    def _handle_sifa_motor_post(self) -> None:
        """СИФА: держатель Сифы включает МоторV8 — раскрытие + уведомление в чат."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        now = time.time()
        with sifa_lock:
            entry = sifa_state.get(chat_id) or {}
            name = str(payload.get("name", ""))[:64]
            sk = resolve_ship_key(entry.get("ships") or {}, user, name)
            ship = (entry.get("ships") or {}).get(sk) if sk else None
            if not ship or not ship.get("sifa"):
                self._json_response(403, {"error": "МоторV8 — только у того, кто держит Сифу"})
                return
            ship["motor_until"] = now + SIFA_MOTOR_SEC
            ship["ts"] = now
        sifa_save_to_github()
        try:
            _who = (tg_mention(ship["tid"], name) if ship.get("tid")
                    else geo_mention(chat_id, sk, name))
            tg_send_with_cleanup(chat_id,
                f"🚤💨 {_who} активировал МоторV8 — 10 минут скорость ×3! "
                "Сифа обозначила себя и сама охотится на касаток! 🐬😱",
                600, html_mode=True)
        except Exception as e:
            print(f"[paint_bot] sifa motor notify: {e!r}", flush=True)
        self._json_response(200, {"ok": True, "motor_until": ship["motor_until"]})

    def _handle_sifa_exit_post(self) -> None:
        """СИФА (устаревшее): корабль убрать нельзя — он остаётся навсегда."""
        self._json_response(410, {"error": "кораблик остаётся на карте навсегда"})

    def _handle_walker_move_post(self) -> None:
        """СЛЕДОПЫТ: идти к точке по суше (маршрут по маске, энергия списывается в конце)."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
            lat = float(payload["lat"])
            lon = float(payload["lon"])
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if not walker_area_ok(lat, lon):
            self._json_response(422, {"error": "это за границами территории Следопыта (Россия)"})
            return
        if not sifa_is_land(lat, lon):
            self._json_response(422, {"error": "человечек по воде не ходит — выбери точку на суше"})
            return
        name = str(payload.get("name", ""))[:64]
        now = time.time()
        with walker_lock:
            with geo_lock:
                mkey = resolve_marker_key(chat_id, user, name)
            if mkey is None:
                self._json_response(403, {"error": "сначала поставь метку на карте"})
                return
            w = walker_state.get(chat_id, {}).get(mkey)
            if w is None:
                self._json_response(404, {"error": "следопыта ещё нет — нажми 🚶 в панели режимов"})
                return
            if walker_progress(w):
                walker_save_to_github()
                klad_on_arrival(chat_id, mkey, w)
            if w.get("route"):
                self._json_response(409, {"error": "человечек уже идёт — дождись, куда шёл"})
                return
            route = walker_land_route(w["lat"], w["lon"], lat, lon)
            if not route:
                self._json_response(422, {"error": "по суше туда не добраться — вокзал или другая цель"})
                return
            km = _walker_route_km(w["lat"], w["lon"], route)
            if km > w.get("energy", 0.0) + 0.5:
                self._json_response(403, {"error": (
                    f"не хватит сил: путь {int(km)} км, а энергии только "
                    f"{int(w.get('energy', 0))} — подкрепись 🍖"
                )})
                return
            w["route"] = route
            w["nav_from_lat"], w["nav_from_lon"] = w["lat"], w["lon"]
            w["nav_ts"] = now
            w["ts"] = now
            walker_save_to_github()
        logline(f"200 /walkermove chat={chat_id} user={mkey!r} km={int(km)}")
        self._json_response(200, {"eta_min": int(km / WALKER_SPEED_KM_PER_MIN) + 1,
                                  "km": round(km, 1)})

    def _handle_walker_food_post(self) -> None:
        """СЛЕДОПЫТ: Пища — готовка (1/час, макс 24/сутки) и приём пищи (+250 км энергии)."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
            act = str(payload.get("act", ""))
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if act not in ("cook", "eat"):
            self._json_response(400, {"error": "act: cook|eat"})
            return
        name = str(payload.get("name", ""))[:64]
        now = time.time()
        today = datetime.datetime.now(MSK_TZ).strftime("%Y-%m-%d")
        if act == "cook":
            with geo_lock:
                mkey = resolve_marker_key(chat_id, user, name)
                if mkey is None:
                    self._json_response(403, {"error": "сначала поставь метку на карте"})
                    return
                marker = geo_state[chat_id][mkey]
                if marker.get("food_day") != today:
                    marker["food_day"] = today
                    marker["food_cooked"] = 0
                left = int(max(0.0, marker.get("food_ready_ts", 0.0) - now))
                if left > 0:
                    self._json_response(429, {"error": (
                        f"плита ещё горячая — следующая порция через {left // 60 + 1} мин"),
                        "retry_in": left})
                    return
                if marker.get("food_cooked", 0) >= FOOD_DAILY_MAX:
                    self._json_response(429, {"error": "на сегодня наготовлено всё (24/24) — завтра снова"})
                    return
                if marker.get("food", 0) >= FOOD_MAX_STOCK:
                    self._json_response(409, {"error": f"сумка с едой полная ({FOOD_MAX_STOCK}/{FOOD_MAX_STOCK})"})
                    return
                marker["food"] = marker.get("food", 0) + 1
                marker["food_cooked"] = marker.get("food_cooked", 0) + 1
                marker["food_ready_ts"] = now + FOOD_COOK_SEC
                geo_save_to_github()
            logline(f"200 /walkerfood cook chat={chat_id} user={mkey!r}")
            self._json_response(200, {"food": marker["food"], "cooked_today": marker["food_cooked"]})
            return
        # eat
        with walker_lock:
            with geo_lock:
                mkey = resolve_marker_key(chat_id, user, name)
            if mkey is None:
                self._json_response(403, {"error": "сначала поставь метку на карте"})
                return
            w = walker_state.get(chat_id, {}).get(mkey)
            if w is None:
                self._json_response(404, {"error": "следопыта ещё нет — нажми 🚶 в панели режимов"})
                return
            with geo_lock:
                marker = geo_state[chat_id][mkey]
                if w.get("energy", 0.0) >= WALKER_ENERGY_MAX - 0.5:
                    self._json_response(409, {"error": "человечек сыт — энергия и так полная"})
                    return
                if marker.get("food", 0) <= 0:
                    self._json_response(404, {"error": "сумка пустая — готовь пищу по кнопке 🍲"})
                    return
                marker["food"] = marker.get("food", 0) - 1
                w["energy"] = min(WALKER_ENERGY_MAX, w.get("energy", 0.0) + WALKER_FOOD_ENERGY)
                w["ts"] = now
            walker_save_to_github()
            geo_save_to_github()
        logline(f"200 /walkerfood eat chat={chat_id} user={mkey!r} energy={int(w['energy'])}")
        self._json_response(200, {"energy": round(w["energy"], 1), "food": marker["food"]})

    def _handle_walker_station_post(self) -> None:
        """СЛЕДОПЫТ: переезд на вокзал — мгновенно, сколько угодно раз, бесплатно."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
            skey = str(payload.get("station", ""))
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        station = next((s for s in WALKER_STATIONS if s["key"] == skey), None)
        if station is None:
            self._json_response(404, {"error": "нет такого вокзала"})
            return
        name = str(payload.get("name", ""))[:64]
        with walker_lock:
            with geo_lock:
                mkey = resolve_marker_key(chat_id, user, name)
            if mkey is None:
                self._json_response(403, {"error": "сначала поставь метку на карте"})
                return
            w = walker_state.get(chat_id, {}).get(mkey)
            if w is None:
                self._json_response(404, {"error": "следопыта ещё нет — нажми 🚶 в панели режимов"})
                return
            slat, slon = _walker_station_point(station)
            w["lat"], w["lon"] = slat, slon
            w["route"] = None
            w["nav_from_lat"] = w["nav_from_lon"] = None
            w["ts"] = time.time()
            walker_save_to_github()
        logline(f"200 /walkerstation chat={chat_id} user={mkey!r} station={skey!r}")
        self._json_response(200, {"lat": slat, "lon": slon, "name": station["name"]})

    def _handle_volcano_post(self, url):
        """Извержение: пользователь целится меткой адресата — от вулкана летит розовая какашка."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
            to_user = str(payload.get("to_user", ""))[:64]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if not user or not to_user or user == to_user:
            self._json_response(400, {"error": "bad request"})
            return
        with geo_lock:
            now = time.time()
            v = volcano_state.get(chat_id)
            if v is None or now - v["spawn_ts"] >= VOLCANO_LIFETIME_SEC:
                self._json_response(404, {"error": "вулкан сейчас не на карте — загляни в следующий час"})
                return
            if v["used"]:
                self._json_response(409, {"error": "вулкан уже извергся — извержений 0"})
                return
            # гость на острове не может извергать какашки
            if island_guest_at(chat_id, user) is not None:
                self._json_response(403, {"error": "ты в отъезде на острове — извержение подождёт 🏝️"})
                return
            dest = geo_state.get(chat_id, {}).get(to_user)
            if dest is None:
                self._json_response(404, {"error": "нет такой метки"})
                return
            v["used"] = True  # первый успевший занимает извержение (кто использовал — не записывается)
            pid = uuid.uuid4().hex[:10]
            total = haversine_km(v["lat"], v["lon"], dest["lat"], dest["lon"])
            poops_state[pid] = {
                "id": pid, "chat": chat_id, "to": to_user,
                "from": user,  # для показа адресата отправителю; в чате автор скрыт
                "to_name": dest.get("name", to_user),
                "from_lat": v["lat"], "from_lon": v["lon"],
                "to_lat": dest["lat"], "to_lon": dest["lon"],
                "start_ts": now, "arrived": False,
            }
        volcano_save_to_github()
        logline(f"200 /volcano chat={chat_id} user={user!r} -> to={to_user!r} id={pid}")
        eta = int(total / poop_speed_km_per_min(poops_state[pid])) + 1
        self._json_response(200, {"eta_min": eta})
        return

    def _handle_meteor_post(self, url):
        """Забрать ЗвезднуюПыль из свежей воронки: +1 на личный баланс, один раз на падение."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if not user:
            self._json_response(400, {"error": "bad request"})
            return
        with geo_lock:
            meteor_check(chat_id)  # переложить просроченную воронку в craters
            m = meteor_state.get(chat_id)
            cur = m.get("current") if m else None
            if cur is None:
                self._json_response(404, {"error": "свежего метеорита нет — жди следующего"})
                return
            if cur["taken"]:
                self._json_response(409, {"error": "пыль уже забрали — остаток ЗП = 0"})
                return
            # гость на острове не может собирать пыль
            if island_guest_at(chat_id, user) is not None:
                self._json_response(403, {"error": "ты в отъезде на острове — метеорит подождёт 🏝️"})
                return
            cur["taken"] = True
            balance = stardust_earn(chat_id, user, 1)
            meteor_save_to_github()
        logline(f"200 /meteor chat={chat_id} user={user!r} balance={balance}")
        self._json_response(200, {"balance": balance})

    def _handle_letter_boost_post(self, url):
        """Ускорить чужое или своё письмо в полёте: −1 ЗП, +30 минут пройденного пути."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
            lid = str(payload.get("id", ""))[:16]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if not user or not lid:
            self._json_response(400, {"error": "bad request"})
            return
        key = f"{chat_id}|{user}"
        if stardust_balance(chat_id, user) < 1:
            self._json_response(403, {"error": "Нет Звездной Пыли для ускорения"})
            return
        with geo_lock:
            letter = letters_state.get(lid)
            if letter is None or letter["chat"] != chat_id:
                self._json_response(404, {"error": "письмо не найдено"})
                return
            _, _, arrived = letter_progress(letter)
            if arrived:
                self._json_response(409, {"error": "письмо уже доставлено — ускорять нечего"})
                return
            balance = stardust_spend(chat_id, user, 1)
            # мгновенное продвижение на 1000 км по траектории: сдвиг start_ts так,
            # чтобы пройденная дистанция выросла ровно на LETTER_BOOST_KM (стакается)
            speed = letter_speed_km_per_min(letter)
            letter["start_ts"] -= (LETTER_BOOST_KM / speed) * 60 if speed > 0 else 0
            letters_save_to_github()
            meteor_save_to_github()
        logline(f"200 /letterboost chat={chat_id} user={user!r} letter={lid} balance={balance}")
        self._json_response(200, {"balance": balance, "boost_km": LETTER_BOOST_KM})

    def _handle_spawnevent_post(self, url):
        """Бета Песочницы: Sumai (или админ) вручную активирует вулкан/метеорит."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
            kind = str(payload.get("kind", ""))[:16]
            name = str(payload.get("name", ""))[:64]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if chat_id != GEO2_CHAT_ID or user not in ("Sumai", str(ADMIN_ID)):
            self._json_response(403, {"error": "спавн событий — только Sumai и только в Песочнице"})
            return
        now = time.time()
        if kind == "volcano":
            with geo_lock:
                lat, lon = random_point_near_moscow(VOLCANO_RADIUS_KM)
                volcano_state[chat_id] = {
                    "lat": lat, "lon": lon, "spawn_ts": now, "used": False,
                    "next_spawn": now + VOLCANO_PERIOD_SEC + random.uniform(0, 3000)}
                volcano_save_to_github()
            try:
                tg_send_with_cleanup(chat_id, VOLCANO_NOTIFY_TEXT, VOLCANO_LIFETIME_SEC)
            except Exception as e:
                print(f"[paint_bot] спавн вулкана: уведомление не ушло: {e!r}", flush=True)
            logline(f"200 /spawnevent volcano chat={chat_id} user={user!r} ({lat:.2f},{lon:.2f})")
            self._json_response(200, {"ok": True, "lat": lat, "lon": lon})
            return
        if kind == "meteor":
            with geo_lock:
                m = meteor_state.get(chat_id)
                if m is None:
                    m = {"current": None, "craters": [], "next_fall": 0.0}
                lat, lon = random_point_anywhere()
                m["current"] = {"lat": lat, "lon": lon, "fall_ts": now, "taken": False}
                m["next_fall"] = now + METEOR_PERIOD_SEC + random.uniform(0, 3000)
                meteor_state[chat_id] = m
                meteor_save_to_github()
            try:
                tg_send_with_cleanup(chat_id, METEOR_NOTIFY_TEXT, METEOR_LIFETIME_SEC)
            except Exception as e:
                print(f"[paint_bot] спавн метеорита: уведомление не ушло: {e!r}", flush=True)
            logline(f"200 /spawnevent meteor chat={chat_id} user={user!r} ({lat:.2f},{lon:.2f})")
            self._json_response(200, {"ok": True, "lat": lat, "lon": lon})
            return
        if kind == "storm":
            with geo_lock:
                isl = island_of(chat_id, user, name)
                if isl is None:
                    self._json_response(404, {"error": "сначала купи остров в Песочнице"})
                    return
                isl["storm"] = {"active_until": now + ISLAND_STORM_LIVE_SEC,
                                "collected": []}
                isl["next_storm_ts"] = now + ISLAND_STORM_PERIOD_SEC
                islands_save_to_github()
            logline(f"200 /spawnevent storm chat={chat_id} user={user!r}")
            self._json_response(200, {"ok": True})
            return
        if kind == "log":
            with sifa_lock:
                entry = _sifa_entry(chat_id)
                lat, lon = sifa_random_water(entry.get("area"))
                logs = entry.get("logs") or []
                entry["logs"] = logs + [{"lat": round(lat, 6), "lon": round(lon, 6)}]
                sifa_save_to_github()
            logline(f"200 /spawnevent log chat={chat_id} user={user!r} ({lat:.2f},{lon:.2f})")
            self._json_response(200, {"ok": True, "lat": lat, "lon": lon})
            return
        self._json_response(400, {"error": "kind: volcano|meteor|storm|log"})

    def _handle_subgift_post(self, url):
        """Отправка подарка: пользователь целится меткой адресата — от кита поплывёт подарок."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
            name = (str(payload.get("name"))[:32]).strip() or "Аноним"
            to_user = str(payload.get("to_user", ""))[:64]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if not user or not to_user or user == to_user:
            self._json_response(400, {"error": "bad request"})
            return
        with geo_lock:
            now = time.time()
            s = submarine_state.get(chat_id)
            if s is None or now - s["spawn_ts"] >= SUBMARINE_LIFETIME_SEC:
                self._json_response(404, {"error": "кит уже уплыл в глубину — загляни в следующий час"})
                return
            if s["used"]:
                self._json_response(409, {"error": "подарок уже отправлен — на этом ките мест больше нет"})
                return
            # гость на острове не может отправлять подарки
            if island_guest_at(chat_id, user) is not None:
                self._json_response(403, {"error": "ты в отъезде на острове — кит подождёт 🏝️🐳"})
                return
            dest = geo_state.get(chat_id, {}).get(to_user)
            if dest is None:
                self._json_response(404, {"error": "нет такой метки"})
                return
            s["used"] = True  # на одну лодку — один подарок (кто отправил — не записывается)
            gid = uuid.uuid4().hex[:10]
            total = haversine_km(s["lat"], s["lon"], dest["lat"], dest["lon"])
            gifts_state[gid] = {
                "id": gid, "chat": chat_id, "from": user, "from_name": name,
                "to": to_user, "to_name": dest.get("name", to_user),
                "from_lat": s["lat"], "from_lon": s["lon"],
                "to_lat": dest["lat"], "to_lon": dest["lon"],
                "start_ts": now, "arrived": False,
            }
        submarine_save_to_github()
        logline(f"200 /subgift chat={chat_id} user={user!r} -> to={to_user!r} id={gid}")
        eta = int(total / gift_speed_km_per_min(gifts_state[gid])) + 1
        self._json_response(200, {"eta_min": eta})
        return

    def _handle_subopen_post(self, url):
        """Открыть доставленный подарок (только адресат): выпадает эмодзи-картинка."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
            gid = str(payload.get("id", ""))[:16]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        with geo_lock:
            gift = gifts_state.get(gid)
            if gift is None or gift["chat"] != chat_id:
                self._json_response(404, {"error": "подарок не найден"})
                return
            if not viewer_matches(gift["to"], user,
                                  str(payload.get("name", ""))[:64], chat_id):
                self._json_response(403, {"error": "этот подарок не тебе"})
                return
            _, _, arrived = gift_progress(gift)
            if not arrived:
                self._json_response(409, {"error": "подарок ещё в пути"})
                return
            if gift.get("opened"):
                self._json_response(200, {"picture": gift["picture"],
                                          "from": gift_sender_name(chat_id, gift),
                                          "re_open": True})
                return
            gift["opened"] = True
            gift["picture"] = random.choice(GIFT_PICS)
            submarine_save_to_github()
        logline(f"200 /subopen chat={chat_id} user={user!r} gift={gid}")
        self._json_response(200, {"picture": gift["picture"],
                                  "from": gift_sender_name(chat_id, gift)})
        return

    # ---------- Остров: покупка, гости на самолёте, постройки, удобрения ----------

    def _handle_island_post(self, url):
        if url.path == "/islandbuy":
            self._island_buy(url)
        elif url.path == "/islandinvite":
            self._island_invite(url)
        elif url.path == "/islandleave":
            self._island_leave(url)
        elif url.path == "/islandbuild":
            self._island_build(url)
        elif url.path == "/islandpoop":
            self._island_poop(url)
        elif url.path == "/islanddel":
            self._island_del(url)
        elif url.path == "/islandrock":
            self._island_rock(url)
        elif url.path == "/islandstorm":
            self._island_storm(url)
        elif url.path == "/islandkick":
            self._island_kick(url)
        elif url.path == "/shipbuild":
            self._ship_build()
        elif url.path == "/shipnav":
            self._ship_nav()
        elif url.path == "/shipboard":
            self._ship_board()
        elif url.path == "/shipready":
            self._ship_ready()
        elif url.path == "/shippick":
            self._ship_pick()
        elif url.path == "/shipduelseen":
            self._ship_duel_seen()
        else:
            self._json_response(404, {"error": "not found"})

    # ---------- Морской Рынок: захват локации и обмен подарков ----------

    def _handle_market_post(self, url):
        """Захватить рынок (/marketcapture) или обменять подарки на ресурсы (/marketexchange)."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
            name = str(payload.get("name", ""))[:64]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        with geo_lock:
            mkey = resolve_marker_key(chat_id, user, name)
            if mkey is None:
                self._json_response(404, {"error": "сначала поставь метку на карте"})
                return
            entry = market_state.setdefault(
                chat_id, {"owner": None, "owner_name": None, "captured_ts": 0.0})
            if url.path == "/marketcapture":
                if entry.get("owner") and viewer_matches(entry["owner"], user, name, chat_id):
                    self._json_response(409, {"error": "рынок уже твой — торгуйся 🎪"})
                    return
                # захват только вплотную к рынку: живой галеон атакующего
                # должен быть в радиусе абордажа (как кнопка ⚔️)
                my_ship = ships_state.get(ship_key(chat_id, mkey))
                if (my_ship is None or my_ship.get("sunk")
                        or haversine_km(my_ship["lat"], my_ship["lon"],
                                        MARKET_LAT, MARKET_LON) > SHIP_BOARD_KM):
                    self._json_response(403, {"error": (
                        "🏴‍☠️ Захватить рынок можно только вплотную! "
                        f"Подплыви на Галеоне в радиус {int(SHIP_BOARD_KM)} км "
                        "от Морского Рынка 🎪"
                    )})
                    return
                cur_ship = (ships_state.get(ship_key(chat_id, entry["owner"]))
                            if entry.get("owner") else None)
                if cur_ship is not None and not cur_ship.get("sunk"):
                    owner_name = entry.get("owner_name") or "?"
                    self._json_response(403, {"error": (
                        f"🎪 Морской Рынок охраняется! У владельца {owner_name} ещё плавает "
                        f"Галеон — сначала потопи его в честном абордаже ⚔️, "
                        f"а потом приплыви сюда и захвати рынок 🏴‍☠️"
                    )})
                    return
                prev_name = entry.get("owner_name")
                prev_owner = entry.get("owner")
                if prev_owner:
                    # накопитель часов владения (для статистики недели): старому владельцу
                    # добиваем время от захвата до смены владельца (в часах)
                    oh = entry.setdefault("owner_hours", {})
                    oh[prev_owner] = oh.get(prev_owner, 0.0) + max(
                        0.0, time.time() - float(entry.get("captured_ts") or time.time())) / 3600.0
                marker = geo_state.get(chat_id, {}).get(mkey) or {}
                entry["owner"] = mkey
                entry["owner_name"] = marker.get("name", mkey)
                entry["captured_ts"] = time.time()
                market_save_to_github()
                cap_name = entry["owner_name"]
            elif url.path == "/marketexchange":
                if not entry.get("owner") or not viewer_matches(entry["owner"], user, name, chat_id):
                    self._json_response(403, {"error": "рынок не твой — сначала захвати 🏴‍☠️"})
                    return
                my_gifts = [g for g in list(gifts_state.values())
                            if g["chat"] == chat_id and g.get("opened") and g.get("picture")
                            and viewer_matches(g["to"], user, name, chat_id)]
                if len(my_gifts) < MARKET_GIFT_COST:
                    self._json_response(403, {"error": (
                        f"на обмен нужно {MARKET_GIFT_COST * 2} эмодзи подарков 🎁 "
                        f"(у тебя — {len(my_gifts) * 2})"
                    )})
                    return
                for g in my_gifts[:MARKET_GIFT_COST]:
                    del gifts_state[g["id"]]  # подарки сгорают в торговых печах
                marker = geo_state.get(chat_id, {}).get(mkey)
                if marker is not None:
                    marker["wood"] = marker.get("wood", 0) + 1
                    marker["poops"] = marker.get("poops", 0) + 1
                stardust_earn(chat_id, mkey, 1)
                submarine_save_to_github()
                geo_save_to_github()
                market_save_to_github()
                logline(f"200 /marketexchange chat={chat_id} user={mkey!r}")
                self._json_response(200, {"ok": True, "spent": MARKET_GIFT_COST})
                return
            else:
                self._json_response(404, {"error": "not found"})
                return
        # уведомление в чат — только при захвате (вне лока: Telegram долго думает)
        _cap = geo_mention(chat_id, mkey, cap_name)
        _prev = geo_mention(chat_id, prev_owner, prev_name) if prev_name else prev_name
        if prev_name and prev_name != cap_name:
            text = (f"🎪 Морской Рынок сменил хозяина! Теперь за прилавком {_cap} — "
                    f"{_prev} отправился кормить рыб 🦈")
        else:
            text = (f"🎪 Морской Рынок впервые захвачен! Хозяин прилавка — {_cap}. "
                    f"Торгуй, пока Галеон цел ⚓😎")
        try:
            tg_send_with_cleanup(chat_id, text, 600, html_mode=True)
        except Exception as e:
            print(f"[paint_bot] уведомление о захвате рынка не ушло: {e!r}", flush=True)
        logline(f"200 /marketcapture chat={chat_id} user={mkey!r}")
        self._json_response(200, {"ok": True})

    # ---------- Корабли (Галеоны): постройка, плавание, абордаж ----------

    def _ship_payload(self):
        length = int(self.headers.get("Content-Length", 0))
        payload = json.loads(self.rfile.read(length).decode("utf-8"))
        return (int(payload["chat"]), str(payload["user"])[:64],
                str(payload.get("name", ""))[:64], payload)

    def _ship_build(self):
        """Построить Галеон на верфи: 1 дерево (временно), один корабль у игрока (живой)."""
        try:
            chat_id, user, name, _ = self._ship_payload()
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        with geo_lock:
            mkey = resolve_marker_key(chat_id, user, name)
            marker = geo_state.get(chat_id, {}).get(mkey) if mkey else None
            if marker is None:
                self._json_response(404, {"error": "сначала поставь метку на карте"})
                return
            isl = island_of(chat_id, mkey, "")
            if isl is None:
                self._json_response(404, {"error": "сначала купи остров (10 ЗП)"})
                return
            if "shipyard" not in isl.get("buildings", []):
                self._json_response(403, {"error": "сначала построй Верфь ⚓ (3 ур., 30 дерева)"})
                return
            if (marker.get("wood", 0)) < SHIP_COST_WOOD:
                self._json_response(403, {"error": f"нужно {SHIP_COST_WOOD} дерева (есть {marker.get('wood', 0)})"})
                return
            old = ships_state.get(ship_key(chat_id, mkey))
            if old is not None and not old.get("sunk"):
                self._json_response(409, {"error": "у тебя уже есть корабль — он один. Потопи его в бою 😈"})
                return
            if old is not None and old.get("sunk"):
                # пауза после потопления: капитан оплакивает экипаж, верфь остывает
                left = SHIP_REBUILD_DELAY_SEC - (time.time() - old.get("sunk_ts", 0))
                if left > 0:
                    self._json_response(403, {"error": (
                        f"верфь остывает после потопления: новый Галеон — "
                        f"через {int(left // 60)} мин {int(left % 60)} сек ⏳"
                    )})
                    return
                # тонувший корабль уходит «мемориальным рифом» — на карте остаётся
                wkey = f"{chat_id}|{mkey}|{int(old.get('sunk_ts', time.time()))}"
                wrecks_state[wkey] = dict(old)
            marker["wood"] = marker.get("wood", 0) - SHIP_COST_WOOD
            marker["ships_built"] = marker.get("ships_built", 0) + 1
            ships_state[ship_key(chat_id, mkey)] = {
                "chat": chat_id, "user": mkey, "name": marker.get("name", mkey),
                "lat": isl["lat"], "lon": isl["lon"],
                "to_lat": None, "to_lon": None,
                "nav_from_lat": None, "nav_from_lon": None, "nav_ts": 0,
                "route": None,
                "sunk": False, "sunk_ts": 0, "wins": 0,
            }
            ships_save_to_github()
            geo_save_to_github()
            wrecks_save_to_github()
        try:
            tg_send_with_cleanup(
                chat_id,
                f"⛵ С верфи острова «{isl.get('name', '?')}» спущен на воду Галеон "
                f"капитана {geo_mention(chat_id, mkey, marker.get('name', mkey))}! "
                "Море теперь не безопасно… 🏴‍☠️",
                600,
                html_mode=True,
            )
        except Exception as e:
            print(f"[paint_bot] уведомление о спуске галеона не ушло: {e!r}", flush=True)
        logline(f"200 /shipbuild chat={chat_id} user={mkey!r}")
        self._json_response(200, {"ok": True})

    def _ship_nav(self):
        """Отправить корабль в точку: только вода, не в бою."""
        try:
            chat_id, user, name, payload = self._ship_payload()
            lat = float(payload["lat"]); lon = float(payload["lon"])
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        with geo_lock:
            sh = ship_of(chat_id, user, name)
            if sh is None:
                self._json_response(404, {"error": "у тебя нет корабля — построй на верфи ⚓"})
                return
            if sh.get("sunk"):
                self._json_response(409, {"error": "твой корабль на дне… строй новый"})
                return
            if ship_in_duel(chat_id, sh["user"]):
                self._json_response(409, {"error": "в бою корабль не слушается руля!"})
                return
            if not (-85.0 <= lat <= 85.0) or not (-180.0 <= lon <= 180.0) or sifa_is_land(lat, lon):
                self._json_response(403, {"error": "корабль плавает только по воде 🌊"})
                return
            ship_progress(sh)
            route = ship_water_route(sh["lat"], sh["lon"], lat, lon)
            if route is None:
                self._json_response(403, {"error": "до этой точки нет водного пути — "
                                                    "Галеон туда не доплывёт 🌊"})
                return
            sh["to_lat"], sh["to_lon"] = lat, lon
            sh["nav_from_lat"], sh["nav_from_lon"] = sh["lat"], sh["lon"]
            sh["route"] = route
            sh["nav_ts"] = time.time()
            ships_save_to_github()
        self._json_response(200, {"ok": True})

    def _ship_board(self):
        """Абордаж: создать/подключиться к дуэли КНБ с ближайшим кораблём (≤500 км)."""
        try:
            chat_id, user, name, _ = self._ship_payload()
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        with geo_lock:
            me = ship_of(chat_id, user, name)
            if me is None or me.get("sunk"):
                self._json_response(404, {"error": "у тебя нет корабля"})
                return
            d = ship_in_duel(chat_id, me["user"])
            if d is not None and d.get("cpu") and d[d["cpu"]] == me["user"]:
                # неявившийся капитан пытается вернуться — его место уже заняла команда
                self._json_response(409, {"error": "поздно! твоя команда уже дерётся без тебя 🤖"})
                return
            if d is None:
                rival = None
                for k2, sh2 in ships_state.items():
                    if sh2.get("chat") != chat_id or sh2.get("sunk") or sh2["user"] == me["user"]:
                        continue
                    if haversine_km(me["lat"], me["lon"], sh2["lat"], sh2["lon"]) <= SHIP_BOARD_KM:
                        rival = sh2
                        break
                if rival is None:
                    self._json_response(409, {"error": f"рядом нет враждебных кораблей (нужно ≤{int(SHIP_BOARD_KM)} км)"})
                    return
                pair = "|".join(sorted([me["user"], rival["user"]]))
                d = ship_duels.get(f"{chat_id}|{pair}")
                if d is not None and d["phase"] == "finished":
                    d = None   # прошлый бой окончен — этот абордаж начинает новую дуэль
                if d is None:
                    d = {
                        "id": f"{chat_id}|{pair}", "chat": chat_id,
                        "a": me["user"], "b": rival["user"],
                        "a_name": me.get("name", me["user"]),
                        "b_name": rival.get("name", rival["user"]),
                        "phase": "ready", "ts": time.time(), "ready": [],
                        "round": 1, "wins": {"a": 0, "b": 0},
                        "pa": None, "pb": None, "last": None,
                    }
                    ship_duels[d["id"]] = d
                    duels_save_to_github()
                    logline(f"ship duel start chat={chat_id} {d['a_name']} vs {d['b_name']}")
                    try:
                        tg_send_with_cleanup(
                            chat_id,
                            f"⚔️ АБОРДАЖ! Капитан {geo_mention(chat_id, d['a'], d['a_name'])} взял "
                            f"на абордаж капитана {geo_mention(chat_id, d['b'], d['b_name'])}! "
                            "Морская волчица готовит зубы, а кто-то из них очень скоро кормит "
                            "рыб… 🦈",
                            600,
                            html_mode=True,
                        )
                    except Exception as e:
                        print(f"[paint_bot] уведомление об абордаже не ушло: {e!r}", flush=True)
            duel_tick(d, time.time())
        self._json_response(200, public_duel(d, me["user"]))

    def _ship_duel_seen(self):
        """Игрок закрыл финальный экран дуэли — больше не показывать (даже после
        перезагрузки страницы, пока дуэль живёт в памяти сервера)."""
        try:
            chat_id, user, name, _ = self._ship_payload()
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        with geo_lock:
            me = ship_of(chat_id, user, name)
            d = None
            if me:
                for dd in ship_duels.values():
                    if (dd["chat"] == chat_id and me["user"] in (dd["a"], dd["b"])
                            and dd["phase"] == "finished"):
                        d = dd
                        break
            if d is not None and me["user"] not in d.setdefault("seen_by", []):
                d["seen_by"].append(me["user"])
                duels_save_to_github()
        self._json_response(200, {"ok": True})

    def _ship_ready(self):
        """Готов к бою."""
        try:
            chat_id, user, name, _ = self._ship_payload()
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        with geo_lock:
            me = ship_of(chat_id, user, name)
            d = ship_in_duel(chat_id, me["user"]) if me else None
            if d is None:
                self._json_response(404, {"error": "дуэль не найдена"})
                return
            if me["user"] not in d["ready"]:
                d["ready"].append(me["user"])
            duel_tick(d, time.time())
        self._json_response(200, public_duel(d, me["user"]))

    def _ship_pick(self):
        """Ход в КНБ: r/s/p."""
        try:
            chat_id, user, name, payload = self._ship_payload()
            pick = str(payload.get("pick", ""))[:1]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if pick not in ("r", "s", "p"):
            self._json_response(400, {"error": "bad pick"})
            return
        with geo_lock:
            me = ship_of(chat_id, user, name)
            d = ship_in_duel(chat_id, me["user"]) if me else None
            if d is None or d["phase"] != "pick":
                self._json_response(409, {"error": "сейчас ход не принимается"})
                return
            side = "a" if d["a"] == me["user"] else "b"
            if d["p" + side] is None:
                d["p" + side] = pick
            duel_tick(d, time.time())
        self._json_response(200, public_duel(d, me["user"]))

    def _island_del(self, url):
        """Удалить свой остров. Нельзя, пока на острове гость (или его самолёт в пути)."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if not user:
            self._json_response(400, {"error": "bad request"})
            return
        name = str(payload.get("name", ""))[:64]
        with geo_lock:
            isl = island_of(chat_id, user, name)
            if isl is None:
                self._json_response(404, {"error": "у тебя нет острова"})
                return
            if isl.get("guest"):
                self._json_response(409, {"error": "пока гость не улетит, остров нельзя удалить"})
                return
            isl_name = isl["name"]
            # стираем запись полностью: остров можно основать заново за 10 ЗП
            del islands_state[f"{chat_id}|{isl['owner']}"]
            islands_save_to_github()
        logline(f"200 /islanddel chat={chat_id} user={user!r} island={isl_name!r}")
        try:
            tg_send_with_cleanup(
                chat_id,
                f"🏝️ Остров «{isl_name}» растворился в океане. "
                f"Была хорошая легенда 🙂 {geo_mention(chat_id, user, name)} может основать "
                "новый — за 10 ЗП.",
                300,
                html_mode=True,
            )
        except Exception as e:
            print(f"[paint_bot] уведомление об удалении острова не ушло: {e!r}", flush=True)
        self._json_response(200, {"ok": True})

    def _island_buy(self, url):
        """Купить остров за ЗП: случайная точка в океане, шутливое имя с ником."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
            name = (str(payload.get("name"))[:32]).strip() or "Аноним"
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if not user:
            self._json_response(400, {"error": "bad request"})
            return
        key = f"{chat_id}|{user}"
        name = str(payload.get("name", ""))[:64]
        with geo_lock:
            if island_of(chat_id, user, name) is not None:
                self._json_response(409, {"error": "у тебя уже есть остров (можешь быть совладельцем)"})
                return
            if stardust_balance(chat_id, user, name) < ISLAND_COST_ZP:
                self._json_response(403, {"error": f"нужно {ISLAND_COST_ZP} ЗП — собирай с метеоритов ☄️"})
                return
            lat, lon = random_ocean_point()
            isl_name = random.choice(ISLAND_NAME_TEMPLATES).format(name=name)
            islands_state[key] = {
                "chat": chat_id, "owner": user, "owner_name": name,
                "lat": lat, "lon": lon, "name": isl_name,
                "xp": 0, "visits": 0, "buildings": [],
                "poop_day": "", "poop_today": 0,
                "created_ts": time.time(), "guest": None,
                "owners": [user],
            }
            balance = stardust_spend(chat_id, user, ISLAND_COST_ZP, name)
            islands_save_to_github()
            meteor_save_to_github()
        logline(f"200 /islandbuy chat={chat_id} user={user!r} island={isl_name!r} balance={balance}")
        try:
            tg_send_with_cleanup(
                chat_id,
                f"🏝️ НОВЫЙ ОСТРОВ! На карте чата вырос «{isl_name}». "
                f"Владелец {geo_mention(chat_id, user, name)} вложил {ISLAND_COST_ZP} ЗП и "
                "теперь может звать гостей самолётом ✈️😎",
                300,  # новость короткоживущая — через 5 минут удаляем, остров остаётся
                html_mode=True,
            )
        except Exception as e:
            print(f"[paint_bot] уведомление об острове не ушло: {e!r}", flush=True)
        self._json_response(200, {"name": isl_name, "balance": balance})

    def _island_invite(self, url):
        """Владелец зовёт гостя: самолёт летит ЗА ним, потом везёт на остров."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
            to_user = str(payload.get("to_user", ""))[:64]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if not user or not to_user or user == to_user:
            self._json_response(400, {"error": "bad request"})
            return
        name = str(payload.get("name", ""))[:64]
        with geo_lock:
            isl = island_of(chat_id, user, name)
            if isl is None:
                self._json_response(404, {"error": "сначала купи остров (10 ЗП) — кнопка в твоей метке"})
                return
            if isl.get("guest"):
                self._json_response(409, {"error": "пока гость не улетит, другого позвать нельзя"})
                return
            dest = geo_state.get(chat_id, {}).get(to_user)
            if dest is None:
                self._json_response(404, {"error": "нет такой метки"})
                return
            # гостя нельзя позвать, если он уже на другом острове или в полёте
            # (иначе один игрок оказывается гостем на двух островах сразу)
            gname = dest.get("name", "")
            for i3 in islands_state.values():
                if i3["chat"] != chat_id or i3 is isl:
                    continue
                g3 = i3.get("guest")
                if not (g3 and (g3["user"] == to_user
                                or viewer_matches(g3["user"], to_user, gname, chat_id))):
                    continue
                if g3["leg"] == "staying":
                    self._json_response(409, {"error": (
                        f"{g3.get('name', 'он')} уже гостит на острове "
                        f"«{i3.get('name', '?')}» у {i3.get('owner_name', '?')} — "
                        "сначала пусть улетит домой"
                    )})
                else:
                    self._json_response(409, {"error": (
                        f"{g3.get('name', 'он')} уже в полёте — дождись посадки, потом зови"
                    )})
                return
            guest_name = dest.get("name", to_user)
            isl["guest"] = {
                "chat": chat_id,
                "user": to_user, "name": guest_name, "leg": "to_guest",
                "from_lat": isl["lat"], "from_lon": isl["lon"],
                "to_lat": dest["lat"], "to_lon": dest["lon"],
                "start_ts": time.time(),
            }
            islands_save_to_github()
            total = haversine_km(isl["lat"], isl["lon"], dest["lat"], dest["lon"])
        logline(f"200 /islandinvite chat={chat_id} owner={user!r} guest={to_user!r}")
        eta = int(total / plane_speed_km_per_min(chat_id)) + 1
        self._json_response(200, {"eta_min": eta, "guest_name": guest_name})

    def _island_leave(self, url):
        """Гость на острове жмёт «Улететь»: самолёт везёт его домой."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if not user:
            self._json_response(400, {"error": "bad request"})
            return
        name = str(payload.get("name", ""))[:64]
        with geo_lock:
            found = None
            for isl in islands_state.values():
                if isl["chat"] != chat_id:
                    continue
                g = isl.get("guest")
                if (g and g["leg"] == "staying"
                        and (g["user"] == user
                             or viewer_matches(g["user"], user, name, chat_id))):
                    found = (isl, g)
                    break
            if found is None:
                self._json_response(404, {"error": "ты не гость на острове (или самолёт ещё в пути)"})
                return
            isl, g = found
            dest = geo_state.get(chat_id, {}).get(user)
            if dest is None:
                isl["guest"] = None  # своей метки нет — гость просто исчезает
                islands_save_to_github()
                logline(f"200 /islandleave chat={chat_id} user={user!r} (без метки — исчез)")
                self._json_response(200, {"gone": True})
                return
            g["leg"] = "home"
            g["from_lat"], g["from_lon"] = isl["lat"], isl["lon"]
            g["to_lat"], g["to_lon"] = dest["lat"], dest["lon"]
            g["start_ts"] = time.time()
            islands_save_to_github()
            total = haversine_km(isl["lat"], isl["lon"], dest["lat"], dest["lon"])
        logline(f"200 /islandleave chat={chat_id} user={user!r}")
        eta = int(total / plane_speed_km_per_min(chat_id)) + 1
        self._json_response(200, {"eta_min": eta})

    def _island_build(self, url):
        """Построить здание: уровень острова + цена ЗП (+ какашки для статуи)."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
            bid = str(payload.get("building", ""))[:16]
            name = str(payload.get("name", ""))[:64]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        spec = ISLAND_BUILDINGS.get(bid)
        if spec is None:
            self._json_response(400, {"error": "неизвестная постройка"})
            return
        emoji, bname, need_level, cost_zp, cost_poop = spec[:5]
        cost_wood = spec[5] if len(spec) > 5 else 0
        key = f"{chat_id}|{user}"
        with geo_lock:
            isl = island_of(chat_id, user, name)
            if isl is None:
                self._json_response(404, {"error": "сначала купи остров (10 ЗП)"})
                return
            if bid in isl.get("buildings", []):
                self._json_response(409, {"error": "это уже построено"})
                return
            lvl = island_level(isl)
            if lvl < need_level:
                self._json_response(403, {"error": f"нужен {need_level} уровень острова (сейчас {lvl})"})
                return
            if stardust_balance(chat_id, user, name) < cost_zp:
                self._json_response(403, {"error": f"нужно {cost_zp} ЗП (баланс {stardust_balance(chat_id, user, name)})"})
                return
            mkey = resolve_marker_key(chat_id, user, name)
            marker = geo_state.get(chat_id, {}).get(mkey) if mkey else None
            if cost_wood:
                have_w = (marker or {}).get("wood", 0)
                if have_w < cost_wood:
                    self._json_response(403, {"error": f"нужно {cost_wood} дерева (есть {have_w})"})
                    return
            if cost_poop:
                have = (marker or {}).get("poops", 0)
                if have < cost_poop:
                    self._json_response(403, {"error": f"нужно {cost_poop} розовых какашек (есть {have})"})
                    return
            balance = stardust_spend(chat_id, user, cost_zp, name)
            if cost_poop and marker is not None:
                marker["poops"] = marker.get("poops", 0) - cost_poop
            if cost_wood and marker is not None:
                marker["wood"] = marker.get("wood", 0) - cost_wood
            isl.setdefault("buildings", []).append(bid)
            islands_save_to_github()
            meteor_save_to_github()
            geo_save_to_github()
            level = island_level(isl)
        logline(f"200 /islandbuild chat={chat_id} user={user!r} building={bid} balance={balance}")
        self._json_response(200, {"balance": balance, "buildings": isl["buildings"],
                                  "level": level, "emoji": emoji, "name": bname})

    def _island_poop(self, url):
        """Удобрить остров розовой какашкой: −1 какашка со счётчика, +1 опыт (лимит 5/сутки)."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if not user:
            self._json_response(400, {"error": "bad request"})
            return
        key = f"{chat_id}|{user}"
        name = str(payload.get("name", ""))[:64]
        with geo_lock:
            isl = island_of(chat_id, user, name)
            if isl is None:
                self._json_response(404, {"error": "сначала купи остров (10 ЗП)"})
                return
            marker_key = resolve_marker_key(chat_id, user, name)
            marker = geo_state.get(chat_id, {}).get(marker_key) if marker_key else None
            have = (marker or {}).get("poops", 0)
            if have < 1:
                self._json_response(403, {"error": "нет розовых какашек — лови из вулкана 🌋"})
                return
            today = datetime.datetime.now(MSK_TZ).strftime("%Y-%m-%d")
            if isl.get("poop_day") != today:
                isl["poop_day"] = today
                isl["poop_today"] = 0
            if isl.get("poop_today", 0) >= ISLAND_POOP_PER_DAY:
                self._json_response(403, {"error": f"лимит: {ISLAND_POOP_PER_DAY} какашек в сутки на остров"})
                return
            marker["poops"] = have - 1
            isl["poop_today"] = isl.get("poop_today", 0) + 1
            isl["xp"] = isl.get("xp", 0) + 1
            islands_save_to_github()
            geo_save_to_github()
            xp, level, poops_left = isl["xp"], island_level(isl), marker["poops"]
        logline(f"200 /islandpoop chat={chat_id} user={user!r} xp={xp}")
        self._json_response(200, {"xp": xp, "level": level, "poops_left": poops_left,
                                  "poop_today": isl["poop_today"], "poop_limit": ISLAND_POOP_PER_DAY})

    def _island_rock(self, url):
        """Скала посланий: чтение всеми, запись — гостем (одно послание на остров)."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            owner = str(payload.get("owner", ""))[:64]
            user = str(payload["user"])[:64]
            text = str(payload.get("text", ""))[:40]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if not owner or not user:
            self._json_response(400, {"error": "bad request"})
            return
        with geo_lock:
            isl = islands_state.get(f"{chat_id}|{owner}")
            if isl is None:
                self._json_response(404, {"error": "нет такого острова"})
                return
            insc = isl.setdefault("inscriptions", [])
            name = str(payload.get("name", ""))[:64]
            mkey = resolve_marker_key(chat_id, user, name)
            # скала — для владельцев (включая совладельцев) и гостя, который СЕЙЧАС на острове
            owners = isl.get("owners") or [owner]
            g = isl.get("guest")
            is_guest = bool(g and g["leg"] == "staying"
                            and (g["user"] == user
                                 or (mkey is not None and g["user"] == mkey)
                                 or viewer_matches(g["user"], user, name, chat_id)))
            is_owner = (mkey is not None and mkey in owners)
            if not is_owner and not is_guest:
                self._json_response(403, {"error": "послания на скале видят только владелец "
                                                "и гость, который сейчас на острове 🪨"})
                return
            already = any(i.get("user") in (user, mkey) or i.get("uid") == user
                          for i in insc)
            if not text:   # чтение
                can_write = (is_guest and mkey not in owners and not already)
                self._json_response(200, {"inscriptions": insc, "can_write": can_write})
                return
            # запись — только гость на острове (владелец на своей скале не пишет)
            if not is_guest:
                self._json_response(403, {"error": "писать может только гость, "
                                                "который сейчас на острове"})
                return
            if mkey is None:
                self._json_response(403, {"error": "сначала поставь метку на карте"})
                return
            marker = geo_state[chat_id][mkey]
            text = text.strip()
            if not (1 <= len(text) <= 20):
                self._json_response(400, {"error": "послание — от 1 до 20 символов"})
                return
            if already:
                self._json_response(409, {"error": "у тебя уже есть послание на этой скале"})
                return
            if len(insc) >= 60:
                self._json_response(409, {"error": "скала заполнена — мест больше нет"})
                return
            insc.append({"user": mkey, "uid": user, "name": marker.get("name", user),
                         "text": text, "ts": time.time()})
            islands_save_to_github()
            logline(f"200 /islandrock chat={chat_id} owner={owner!r} user={user!r}")
        self._json_response(200, {"ok": True, "count": len(insc)})

    def _island_storm(self, url):
        """Шторм: собрать выброшенное на берег дерево (владелец или гость на острове)."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if not user:
            self._json_response(400, {"error": "bad request"})
            return
        name = str(payload.get("name", ""))[:64]
        mkey = resolve_marker_key(chat_id, user, name)
        now = time.time()
        with geo_lock:
            isl = island_of(chat_id, user, name)
            if isl is None:
                for i2 in islands_state.values():
                    if i2["chat"] != chat_id:
                        continue
                    g2 = i2.get("guest")
                    if (g2 and g2["leg"] == "staying"
                            and (g2["user"] == user
                                 or viewer_matches(g2["user"], user, name, chat_id))):
                        isl = i2
                        break
            if isl is None:
                self._json_response(404, {"error": "у тебя нет острова и ты не гость"})
                return
            storm = isl.get("storm")
            if not storm or now >= storm.get("active_until", 0):
                self._json_response(410, {"error": "шторм уже стих — волна унесла дерево"})
                return
            collected = storm.get("collected", [])
            if user in collected or (mkey and mkey in collected):
                self._json_response(409, {"error": "ты уже собрал своё дерево с этого шторма"})
                return
            # один игрок — одно дерево за шторм: гость на нескольких островах
            # (или владелец + гость) не может собрать с двух штормов одновременно
            for i3 in islands_state.values():
                if i3["chat"] != chat_id or i3 is isl:
                    continue
                s3 = i3.get("storm")
                if not s3 or now >= s3.get("active_until", 0):
                    continue
                c3 = s3.get("collected") or []
                if user in c3 or (mkey and mkey in c3):
                    self._json_response(409, {"error": (
                        "ты уже собрал дерево с другого шторма — "
                        "одно дерево за шторм, какой бы остров ни трясло 🌊"
                    )})
                    return
            if mkey is None:
                self._json_response(403, {"error": "сначала поставь метку на карте"})
                return
            marker = geo_state[chat_id][mkey]
            marker["wood"] = marker.get("wood", 0) + ISLAND_STORM_WOOD
            storm.setdefault("collected", []).append(mkey)
            wood = marker["wood"]
            islands_save_to_github()
            geo_save_to_github()
        logline(f"200 /islandstorm chat={chat_id} user={user!r} wood={wood}")
        self._json_response(200, {"wood": wood, "got": ISLAND_STORM_WOOD})

    def _island_kick(self, url):
        """Владелец выпроваживает задержавшегося гостя (сутки на острове — предел)."""
        try:
            length = int(self.headers.get("Content-Length", 0))
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            chat_id = int(payload["chat"])
            user = str(payload["user"])[:64]
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        if not user:
            self._json_response(400, {"error": "bad request"})
            return
        now = time.time()
        name = str(payload.get("name", ""))[:64]
        with geo_lock:
            isl = island_of(chat_id, user, name)
            if isl is None:
                self._json_response(404, {"error": "у тебя нет острова"})
                return
            g = isl.get("guest")
            if not g or g["leg"] != "staying":
                self._json_response(404, {"error": "гостя сейчас нет на острове"})
                return
            st = g.get("staying_ts") or g.get("start_ts") or now
            left = int(86400 - (now - st))
            if left > 0:
                self._json_response(403, {"error": f"гостю ещё можно торчать "
                                                f"{left // 3600} ч {left % 3600 // 60} мин"})
                return
            dest = geo_state.get(chat_id, {}).get(g["user"])
            gname = g["name"]
            isl_name = isl["name"]
            if dest is None:
                isl["guest"] = None
                islands_save_to_github()
                logline(f"200 /islandkick chat={chat_id} user={user!r} (гость без метки — исчез)")
                self._json_response(200, {"gone": True})
                return
            g["leg"] = "home"
            g["from_lat"], g["from_lon"] = isl["lat"], isl["lon"]
            g["to_lat"], g["to_lon"] = dest["lat"], dest["lon"]
            g["start_ts"] = now
            islands_save_to_github()
            total = haversine_km(isl["lat"], isl["lon"], dest["lat"], dest["lon"])
        logline(f"200 /islandkick chat={chat_id} owner={user!r} guest={gname!r}")
        try:
            tg_send_with_cleanup(
                chat_id,
                f"👢 {geo_mention(chat_id, g['user'], gname)} задержался на «{isl_name}» "
                f"дольше суток — хозяин отправил его домой ✈️ До встречи!",
                ARRIVAL_NOTIFY_TTL_SEC,
                html_mode=True,
            )
        except Exception as e:
            print(f"[paint_bot] уведомление о кике не ушло: {e!r}", flush=True)
        eta = int(total / plane_speed_km_per_min(chat_id)) + 1
        self._json_response(200, {"eta_min": eta, "guest_name": gname})

    def log_message(self, format, *args):
        pass  # не спамить в логи


def run_http_server():
    port = int(os.environ.get("PORT", "10000"))
    server = ThreadingHTTPServer(("0.0.0.0", port), AppHandler)
    server.serve_forever()


# ---------- Логика игры ----------

def make_secret() -> str:
    """4 разные цифры, первая — не ноль."""
    digits = random.sample("0123456789", 4)
    if digits[0] == "0":
        i = next(i for i, d in enumerate(digits) if d != "0")
        digits[0], digits[i] = digits[i], digits[0]
    return "".join(digits)


def bulls_and_cows(secret: str, guess: str) -> tuple[int, int]:
    bulls = sum(s == g for s, g in zip(secret, guess))
    cows = sum(g in secret for g in guess) - bulls
    return bulls, cows


def valid_guess(text: str) -> str | None:
    """Вернуть текст ошибки, если ввод не похож на 4-значное число."""
    if not (len(text) == 4 and text.isdigit()):
        return "Нужно отправить 4 цифры, например: 1234"
    if text[0] == "0":
        return "Первая цифра не может быть нулём."
    if len(set(text)) < 4:
        return "Цифры не должны повторяться."
    return None


def player_stats(user_id: int) -> dict:
    return stats.setdefault(user_id, {"games": 0, "wins": 0, "best": None})


def display_name(user) -> str:
    return f"@{user.username}" if user.username else (user.first_name or str(user.id))


def remember_user(user) -> None:
    if user and user.username:
        users_by_name[user.username.lower()] = user.id


def find_user_id(text: str, entities, fallback_user=None) -> int | None:
    """Найти user_id: из reply, по @упоминанию (если пользователь известен) или по числовому id."""
    if fallback_user is not None:
        return fallback_user.id
    for ent in entities or []:
        if ent.type == MessageEntity.MENTION:
            uname = text[ent.offset : ent.offset + ent.length].lstrip("@").lower()
            if ent.user is not None:
                return ent.user.id
            return users_by_name.get(uname)
    # числовой id (с @ или без)
    token = text.split()[-1].lstrip("@")
    if token.isdigit():
        return int(token)
    return None


def parse_ch(text: str) -> str | None:
    """Выделить вариант из сообщения формата ch1234. None — если формат другой."""
    t = text.strip().lower()
    if t.startswith("ch") and t[2:].isdigit():
        return t[2:]
    return None


# ---------- Меню выбора игры и соло-игры ----------

GAME_MENU = InlineKeyboardMarkup(
    [
        [InlineKeyboardButton("🐂 Быки и коровы", callback_data="game:bulls")],
        [InlineKeyboardButton("🎨 Рисовалка", callback_data="game:paint")],
        [InlineKeyboardButton("📜 СагаЧата", callback_data="game:saga")],
    ]
)

INTRO_BULLS = (
    "🎲 Игра «Быки и коровы» против компьютера!\n\n"
    "Я загадал число из 4 разных цифр (первая — не ноль).\n"
    "Называй варианты в формате ch1234 (ch + 4 цифры), а я отвечу:\n"
    "🐂 быки — цифра угадана и стоит на своём месте,\n"
    "🐄 коровы — цифра есть в числе, но стоит не там.\n"
    "Угадай число! /stop — сдаться."
)


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/startsum — показать меню выбора игры."""
    if not chat_allowed(update.effective_chat):
        return  # чужая группа — молчим (предупреждение отправляется при добавлении бота)
    remember_user(update.effective_user)
    menu_rows = [list(row) for row in GAME_MENU.inline_keyboard]
    if update.effective_chat.id in (GEO2_CHAT_ID, ANON_GROUP_ID):
        menu_rows.insert(2, [InlineKeyboardButton("🌍✨ ГеографияЧата 2.0",
                                                callback_data="game:geo2")])
    await update.message.reply_text("🎮 Привет! Выбери игру:",
                                    reply_markup=InlineKeyboardMarkup(menu_rows))


async def cmd_myid(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/myid (в личке) — показать свой числовой ID Telegram."""
    if update.message.chat.type != "private":
        return  # только в личке, чтобы не палить ID в группах
    await update.message.reply_text(f"Твой ID Telegram: {update.effective_user.id}")


async def cmd_geo2(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/geo2 — вход в ГеографиюЧата 2.0. WebApp-кнопки (web_app) Telegram разрешает
    ТОЛЬКО в личке: в группах тот же запрос падает с Button_type_invalid. Обход —
    прямая ссылка Mini App t.me/<bot>/<shortname>?startapp=<chat_id> (открывается
    внутри Telegram из любого чата); нужен shortname из BotFather (env GEO2_APP_SHORTNAME).
    Без него — честный фолбэк: кнопка уходит в ЛС (как через меню /startsum)."""
    if not chat_allowed(update.effective_chat):
        return
    remember_user(update.effective_user)
    chat_id = update.effective_chat.id
    if chat_id not in (GEO2_CHAT_ID, ANON_GROUP_ID):
        await update.message.reply_text("🧪 «ГеографияЧата 2.0» пока доступна только в чатах бета-теста!")
        return
    text = (
        "🌍✨ ГеографияЧата 2.0 — общая карта этого чата: метки, письма, подарки, события.\n"
        "Жми «Открыть карту» — Telegram подписывает тебя лично, играешь от своего имени."
    )
    shortname = os.environ.get("GEO2_APP_SHORTNAME", "").strip()
    if update.message.chat.type != "private" and shortname:
        url = f"https://t.me/{context.bot.username}/{shortname}?startapp={chat_id}"
        await update.message.reply_text(text, reply_markup=InlineKeyboardMarkup(
            [[InlineKeyboardButton("🌍 Открыть карту", url=url)]]))
        return
    if update.message.chat.type == "private":
        await update.message.reply_text(text, reply_markup=geo2_keyboard(chat_id))
        return
    dm_ok, dm_err = await dm_game_button(context, update.effective_user.id, text,
                                         geo2_keyboard(chat_id))
    if dm_ok:
        await update.message.reply_text("🌍✨ Кнопка «Открыть карту» ушла тебе в личку 👌")
    else:
        await update.message.reply_text("🌍✨ Не смог написать в личку: "
                                        + dm_fail_reason(dm_err) + ". Сначала /startsum")


async def dm_game_button(context: ContextTypes.DEFAULT_TYPE, user_id: int, text: str, keyboard):
    """Кнопки WebApp Telegram разрешает только в личке — в группах шлём кнопку в ЛС игроку.
    Возвращает (доставлено, причина_отказа) — причину пишем в лог и показываем в чате."""
    try:
        await context.bot.send_message(user_id, text, reply_markup=keyboard)
        return True, None
    except Exception as e:
        print(f"[paint_bot] ЛС не ушло пользователю {user_id}: {e!r}", flush=True)
        return False, e


def dm_fail_reason(e) -> str:
    """Короткая русская расшифровка причины отказа доставки в ЛС."""
    s = str(e)
    if "blocked" in s:
        return "бот у тебя в заблокированных"
    if "deactivated" in s:
        return "аккаунт неактивен"
    if "initiate" in s:
        return "нет переписки с ботом — нажми /startsum в личке"
    return "сбой доставки"


async def on_game_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Выбор игры в меню: запускает игру с меткой типа; старую игру игрока завершает."""
    if not chat_allowed(update.effective_chat):
        await update.callback_query.answer()
        return
    query = update.callback_query
    await query.answer()
    game_key = query.data.split(":", 1)[1]
    chat_id = query.message.chat_id

    if game_key == "bulls":
        key = (chat_id, query.from_user.id)
        old = solo_games.pop(key, None)
        solo_games[key] = {"type": "bulls", "secret": make_secret(), "attempts": 0, "history": []}
        player_stats(query.from_user.id)["games"] += 1
        note = "\n\n♻️ Прежняя игра завершена." if old is not None else ""
        await query.edit_message_text(INTRO_BULLS + note)
        return

    if game_key == "paint":
        is_private = query.message.chat.type == "private"
        state = paint_state.setdefault(chat_id, new_paint_state())
        state["webapp"] = is_private
        caption = "🎨 Общий лист группы! Рисуем по очереди — каждый добавляет штрих."
        if is_private:
            msg = await context.bot.send_photo(
                chat_id,
                photo=io.BytesIO(state["image"]),
                caption=caption,
                reply_markup=paint_keyboard(chat_id, webapp=True, drawer=state["drawer"]),
            )
            state["msg_id"] = msg.message_id
            await query.edit_message_text("🎨 Рисовалка запущена! Лист выше — жми «Открыть холст».")
            return
        # в группе лист остаётся в чате, а кнопку WebApp шлём в личку (в группах она запрещена)
        msg = await context.bot.send_photo(chat_id, photo=io.BytesIO(state["image"]), caption=caption)
        state["msg_id"] = msg.message_id
        hint = ("🎨 Общий лист твоего чата!\nРисуем по очереди — каждый добавляет штрих. "
                "Жми «Открыть холст» 👇")
        dm_ok, dm_err = await dm_game_button(
            context, query.from_user.id, hint,
            paint_keyboard(chat_id, webapp=True, drawer=state["drawer"]))
        if dm_ok:
            await query.edit_message_text("🎨 Лист в чате выше, а кнопка «Открыть холст» — у тебя в личке 👌")
        else:
            await query.edit_message_text("🎨 Лист в чате выше. Не смог написать в личку: "
                                          + dm_fail_reason(dm_err) + ". Сначала /startsum")
        return

    if game_key == "geo":
        is_private = query.message.chat.type == "private"
        count = len(geo_state.get(chat_id, {}))
        text = (
            "🌍 География чата!\nКаждый участник открывает карту и ставит метку своего города. "
            "Метки общие для этого чата и не видны в других чатах."
            + (f"\nСейчас меток: {count}." if count else "")
        )
        if is_private:
            await context.bot.send_message(chat_id, text, reply_markup=geo_keyboard(chat_id, True))
            await query.edit_message_text("🌍 Карта запущена — жми «Открыть карту» выше.")
            return
        dm_ok, dm_err = await dm_game_button(context, query.from_user.id, text,
                                             geo_keyboard(chat_id, False))
        if dm_ok:
            await query.edit_message_text("🌍 Карта запущена — кнопка «Открыть карту» ушла тебе в личку 👌")
        else:
            await query.edit_message_text("🌍 Не смог написать в личку: "
                                          + dm_fail_reason(dm_err) + ". Сначала /startsum")
        return

    if game_key == "geo2":
        if chat_id not in (GEO2_CHAT_ID, ANON_GROUP_ID):
            await query.answer("🧪 «ГеографияЧата 2.0» пока доступна только в чатах бета-теста!",
                               show_alert=True)
            return
        text = (
            "🌍✨ ГеографияЧата 2.0 — переработанный интерфейс карты!\n"
            "Те же метки, письма, подарки и события, что и в Географии чата, "
            "— но в новом обновлённом интерфейсе."
        )
        if query.message.chat.type == "private":
            await context.bot.send_message(chat_id, text, reply_markup=geo2_keyboard(chat_id))
            await query.edit_message_text("🌍✨ Жми «Открыть карту» выше.")
            return
        dm_ok, dm_err = await dm_game_button(context, query.from_user.id, text,
                                             geo2_keyboard(chat_id))
        if dm_ok:
            await context.bot.send_message(chat_id, "🌍✨ Кнопка «Открыть карту» ушла тебе в личку 👌")
        else:
            await context.bot.send_message(chat_id, "🌍✨ Не смог написать в личку: "
                                          + dm_fail_reason(dm_err) + ". Сначала /startsum")
        return

    if game_key == "saga":
        info = (
            "📜 СагаЧата — общая история чата!\n\n"
            "Бот начинает сагу первой главой. Дальше участники продолжают её "
            "по одной главе — сообщением вида:\n"
            "«saga <твоя глава>»\n\n"
            "Правила: глава от 30 до 280 символов; нельзя писать две главы подряд; "
            "авторы анонимны; досрочно заканчивать историю нельзя. "
            f"После {SAGA_MAX_CHAPTERS} глав сага публикуется финальным эпосом."
        )
        s = saga_state.get(chat_id)
        if s is None:
            kb = InlineKeyboardMarkup([[InlineKeyboardButton("📜 Новая Сага", callback_data="saga:new")]])
            await query.edit_message_text(info, reply_markup=kb)
        else:
            n = len(s.get("chapters", []))
            text = (info + "\n\n———\n📜 Сага УЖЕ начата! Глав: "
                    f"{n}/{SAGA_MAX_CHAPTERS}. Жду продолжения «saga <твоя глава>» в чате.")
            kb = InlineKeyboardMarkup([[InlineKeyboardButton("🏁 Завершить Сагу", callback_data="saga:confirm")]])
            await query.edit_message_text(text, reply_markup=kb)
        return

    await query.answer("Эта игра появится позже 🙂", show_alert=True)


async def on_saga_action(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Кнопки саги: saga:new — начать, saga:finish — завершить с публикацией эпоса."""
    if not chat_allowed(update.effective_chat):
        await update.callback_query.answer()
        return
    query = update.callback_query
    await query.answer()
    action = query.data.split(":", 1)[1]
    chat_id = query.message.chat_id
    if action == "new":
        if chat_id in saga_state:
            await query.answer("Сага уже идёт 🙂", show_alert=True)
            return
        zagin = random.choice(SAGA_ZAGINS)
        saga_state[chat_id] = {"chapters": [zagin], "last_author": None,
                               "started_ts": time.time(),
                               "last_chapter_ts": time.time(), "last_nag_ts": 0.0}
        saga_save_to_github()
        await query.edit_message_text(
            f"📜 Сага чата началась! Глава 1/{SAGA_MAX_CHAPTERS}:\n«{zagin}»\n\n"
            "Продолжение — сообщением «saga <твоя глава>». Две главы подряд одним "
            "автором нельзя; авторы анонимны."
        )
        return
    if action == "confirm":
        if chat_id not in saga_state:
            await query.edit_message_text("📜 Саги сейчас нет — начни новую в меню /startsum.")
            return
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton("✅ Да, завершить", callback_data="saga:finish")],
            [InlineKeyboardButton("↩️ Отмена", callback_data="saga:cancel")],
        ])
        await query.edit_message_text(
            "⚠️ Ты точно хочешь прервать текущую Сагу Чата и завершить её?",
            reply_markup=kb)
        return
    if action == "cancel":
        s = saga_state.get(chat_id)
        if s is None:
            await query.edit_message_text("📜 Саги сейчас нет — начни новую в меню /startsum.")
            return
        await query.edit_message_text(
            f"📜 Сага продолжается! Глав: {len(s.get('chapters', []))}/{SAGA_MAX_CHAPTERS}. "
            "Жду «saga <твоя глава>» в чате 🙂")
        return
    # finish
    if chat_id not in saga_state:
        await query.edit_message_text("📜 Саги сейчас нет — начни новую в меню /startsum.")
        return
    await query.edit_message_text("📜 Завершаю сагу и публикую эпос…")
    await saga_publish(context.bot, chat_id)


def paint_keyboard(chat_id: int, webapp: bool = True, drawer: str | None = None) -> InlineKeyboardMarkup | None:
    """Кнопка холста. WebApp-кнопки разрешены только в личке: для групп (webapp=False)
    клавиатура не возвращается — кнопку игроку шлём в ЛС (dm_game_button)."""
    url = f"{APP_URL}/app?chat={chat_id}"
    if drawer:
        # пока кто-то рисует — кнопка не открывает холст, а сообщает, кто рисует
        return InlineKeyboardMarkup([[InlineKeyboardButton(f"🖌 Рисует {drawer}...", callback_data="paint_wait")]])
    if not webapp:
        return None
    return InlineKeyboardMarkup([[InlineKeyboardButton("🖌 Открыть холст", web_app=WebAppInfo(url=url))]])


def geo2_keyboard(chat_id: int) -> InlineKeyboardMarkup:
    """Бета 2.0: кнопка открывает карту как WebApp внутри Telegram."""
    url = f"{APP_URL}/geo2map?chat={chat_id}&v={BUILD_TAG}"
    return InlineKeyboardMarkup([[InlineKeyboardButton("🌍 Открыть карту", web_app=WebAppInfo(url=url))]])


def geo_keyboard(chat_id: int, webapp: bool) -> InlineKeyboardMarkup:
    url = f"{APP_URL}/geomap?chat={chat_id}"
    btn = InlineKeyboardButton("🌍 Открыть карту", web_app=WebAppInfo(url=url))
    return InlineKeyboardMarkup([[btn]])


async def on_paint_wait(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Нажали на кнопку «Рисует ...» — сообщить, что холст занят."""
    if not chat_allowed(update.effective_chat):
        await update.callback_query.answer()
        return
    drawer = (paint_state.get(update.effective_chat.id) or {}).get("drawer")
    if drawer:
        await update.callback_query.answer(f"🖌 Сейчас рисует {drawer}. Подожди немного!", show_alert=True)
    else:
        await update.callback_query.answer("Холст уже свободен — жми «Открыть холст» 🎨", show_alert=True)


async def process_paint_updates(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Раз в секунду применяет события рисовалки: новые рисунки и смену замка «Рисует...»."""
    while True:
        try:
            chat_id = paint_update_queue.get_nowait()
        except queue.Empty:
            return
        state = paint_state.get(chat_id)
        if state is None:
            continue
        # авто-разблокировка, если рисующий завис и не отправил рисунок
        if state.get("drawer") and time.time() - state.get("lock_time", 0) > PAINT_LOCK_TIMEOUT:
            state["drawer"] = None
        markup = paint_keyboard(chat_id, webapp=state.get("webapp", False), drawer=state.get("drawer"))
        if state["msg_id"] is not None:
            try:
                if state.pop("dirty_img", False):
                    media = InputMediaPhoto(media=io.BytesIO(state["image"]))
                    await context.bot.edit_message_media(
                        chat_id=chat_id,
                        message_id=state["msg_id"],
                        media=media,
                        reply_markup=markup,
                    )
                elif state.get("rendered_drawer") != state.get("drawer"):
                    await context.bot.edit_message_reply_markup(
                        chat_id=chat_id, message_id=state["msg_id"], reply_markup=markup
                    )
                state["rendered_drawer"] = state.get("drawer")
                continue
            except BadRequest:
                state["msg_id"] = None  # сообщение удалено — пришлём новое ниже
        try:
            msg = await context.bot.send_photo(
                chat_id,
                photo=io.BytesIO(state["image"]),
                caption="🎨 Общий лист группы!",
                reply_markup=markup,
            )
            state["msg_id"] = msg.message_id
            state["rendered_drawer"] = state.get("drawer")
        except Exception:
            pass


async def paint_periodic_sweep(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Периодически снимает зависшие замки «Рисует...» (даже если в чате тишина)
    и уводит в музей листы, над которыми час никто не работал."""
    now = time.time()
    for chat_id, state in list(paint_state.items()):
        if state.get("drawer") and now - state.get("lock_time", 0) > PAINT_LOCK_TIMEOUT:
            state["drawer"] = None
            paint_update_queue.put(chat_id)  # кнопка «Открыть холст» вернётся
        last = state.get("last_activity")
        if last is not None and now - last > PAINT_IDLE_TIMEOUT:
            try:
                await context.bot.send_photo(
                    chat_id,
                    photo=io.BytesIO(state["image"]),
                    caption="🖼 Финальное творчество вашего чатика. "
                            "Отправляю в Музей Современного Искусства",
                )
            except Exception as e:
                print(f"[paint_bot] музей: не смог забрать рисунок чата {chat_id}: {e!r}", flush=True)
            del paint_state[chat_id]


async def backup_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Ежедневный бэкап меток и писем (сетевые запросы — в отдельном потоке)."""
    await asyncio.to_thread(backup_geo_data)


def end_duel(chat_id: int, user_id: int) -> str | None:
    """Завершить дуэль, если игрок её участник. Вернуть текст результата или None."""
    duel = duels.get(chat_id)
    if duel is None or user_id not in duel["players"]:
        return None
    del duels[chat_id]
    return "⚔️ Дуэль прервана по договорённости. Новая — /playsum @игрок"


def end_paint(chat_id: int) -> str | None:
    """Завершить рисовалку в чате (общий лист). Вернуть текст результата или None."""
    if chat_id not in paint_state:
        return None
    del paint_state[chat_id]
    return "🎨 Рисовалка завершена, общий лист стёрт. Новый — через меню /startsum"


def end_solo(chat_id: int, user_id: int) -> str | None:
    """Завершить соло-игру пользователя. Вернуть текст результата или None."""
    game = solo_games.pop((chat_id, user_id), None)
    if game is None:
        return None
    if game["type"] == "bulls":
        return f"😔 Сдаёшься? Загаданное число было: {game['secret']}.\nНовая игра — /startsum"
    return "Игра завершена.\nНовая игра — /startsum"


def end_geo(chat_id: int) -> str | None:
    """Стереть все метки чата с карты. Вернуть текст результата или None."""
    if not geo_state.get(chat_id):
        return None
    with geo_lock:
        geo_state.pop(chat_id, None)
    geo_save_to_github()
    return "🌍 География чата очищена — все метки стёрты. Новая карта — через меню /startsum"


def close_activity(chat_id: int, user_id: int, kind: str) -> str:
    """Завершить активность по выбору (duel/paint/solo) и вернуть текст для пользователя."""
    if kind == "duel":
        return end_duel(chat_id, user_id) or "Дуэль уже завершена."
    if kind == "paint":
        return end_paint(chat_id) or "Рисовалка уже завершена."
    if kind == "saga":
        return "📜 Сага завершается — публикую эпос…"  # публикация — в вызывающем обработчике
    return end_solo(chat_id, user_id) or "Игра уже завершена."


async def cmd_delpointgeo(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/delpointgeo — СЕКРЕТНАЯ команда админа: стереть все метки чата с карты."""
    if update.effective_user.id != ADMIN_ID:
        return  # для остальных команда невидима
    if not chat_allowed(update.effective_chat):
        return
    text = end_geo(update.message.chat_id) or "🌍 Карта этого чата уже пустая."
    await update.message.reply_text(text)


async def cmd_stop(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/stop — завершить игру; если активно несколько — предложить выбор кнопками."""
    if not chat_allowed(update.effective_chat):
        return
    remember_user(update.effective_user)
    chat_id = update.message.chat_id
    user = update.effective_user

    options = []
    duel = duels.get(chat_id)
    if duel is not None and user.id in duel["players"]:
        options.append(("⚔️ Дуэль", "stop:duel"))
    if chat_id in paint_state:
        options.append(("🎨 Рисовалка", "stop:paint"))
    if (chat_id, user.id) in solo_games:
        options.append(("🐂 Соло «Быки и коровы»", "stop:solo"))
    if chat_id in saga_state:
        options.append(("📜 СагаЧата", "stop:saga"))

    if not options:
        await update.message.reply_text(
            "Нет активных игр. /startsum — меню игр, /playsum @игрок — дуэль."
        )
        return
    if len(options) == 1:
        kind = options[0][1].split(":", 1)[1]
        if kind == "saga":
            await update.message.reply_text("📜 Завершаю сагу — публикую эпос…")
            await saga_publish(context.bot, chat_id)
        else:
            mids = collect_bc_msg_ids(chat_id, user.id, kind)
            await update.message.reply_text(close_activity(chat_id, user.id, kind))
            if mids:
                schedule_bc_cleanup(context, chat_id, mids)
        return
    kb = InlineKeyboardMarkup(
        [[InlineKeyboardButton(label, callback_data=cb)] for label, cb in options]
    )
    await update.message.reply_text("В чате несколько активных игр. Что завершить?", reply_markup=kb)


async def on_stop_choice(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Выбор активности в меню /stop."""
    if not chat_allowed(update.effective_chat):
        await update.callback_query.answer()
        return
    query = update.callback_query
    kind = query.data.split(":", 1)[1]
    if kind == "saga":
        await query.answer()
        await query.edit_message_text("📜 Завершаю сагу — публикую эпос…")
        await saga_publish(context.bot, update.effective_chat.id)
        return
    mids = collect_bc_msg_ids(update.effective_chat.id, query.from_user.id, kind)
    text = close_activity(update.effective_chat.id, query.from_user.id, kind)
    await query.answer()
    await query.edit_message_text(text)
    if mids:
        schedule_bc_cleanup(context, update.effective_chat.id, mids)


HELP_TEXT = (
    "📖 Как играть в «Быки и коровы»\n\n"
    "Бот загадывает число из 4 разных цифр (первая — не ноль). Ты называешь "
    "варианты, а бот отвечает:\n"
    "🐂 быки — цифра угадана и стоит на своём месте,\n"
    "🐄 коровы — цифра есть в числе, но стоит не там.\n\n"
    "✍️ Формат хода: сообщение ch1234 — «ch» и сразу 4 цифры, пробелов нет. "
    "На обычные сообщения бот не реагирует.\n\n"
    "▶️ Игры: /startsum — меню выбора.\n\n"
    "📜 СагаЧата — общая анонимная история чата: продолжение сообщением "
    "«saga <глава>» (30–280 символов, две главы подряд одним автором нельзя, "
    "авторы не раскрываются).\n\n"
    "⚔️ Дуэль двух игроков (в группе):\n"
    "1. Оба игрока один раз открывают меня в личке и нажимают /start.\n"
    "2. В группе вызывающий отвечает (reply) на сообщение противника командой /playsum "
    "(или пишет /playsum @ник — сработает, если тот писал в группе), "
    "противник нажимает «Принять».\n"
    "3. Каждый игрок в ЛИЧКЕ со мной вводит /secret 1234 — своё число (противник его не увидит).\n"
    "4. Когда оба загадали, начинаем: ходы по очереди в группе — пиши ch1234.\n"
    "5. Кто первым угадал число соперника — победил!\n\n"
    "Прервать игру — /stop, статистика — /stats."
)


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/helpsum — справка по игре."""
    if not chat_allowed(update.effective_chat):
        return
    remember_user(update.effective_user)
    await update.message.reply_text(HELP_TEXT)


async def cmd_stats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/stats — статистика игрока."""
    if not chat_allowed(update.effective_chat):
        return
    remember_user(update.effective_user)
    st = player_stats(update.effective_user.id)
    if st["games"] == 0:
        await update.message.reply_text("Ты ещё не играл. /startsum — против компьютера, /playsum @игрок — дуэль.")
        return
    best = f"{st['best']} попыток" if st["best"] is not None else "—"
    await update.message.reply_text(f"📊 Твоя статистика:\nИгр: {st['games']}\nПобед: {st['wins']}\nЛучший результат: {best}")


async def cmd_klad(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/klad — квест «Поиск клада»: загадка, доступные подсказки, тепло/холодно."""
    if not chat_allowed(update.effective_chat):
        return
    chat_id = update.message.chat_id
    now = time.time()
    need_save = False
    with klad_lock:
        entry = klad_state.get(chat_id)
        if not entry or now >= entry["expires_ts"]:
            entry = klad_new(chat_id, save=False)  # save под klad_lock = самодедлок
            need_save = entry is not None
    if need_save:
        klad_save_to_github(force=True)
    if not entry:
        await update.message.reply_text("🏴‍☠️ Клад сейчас недоступен — попробуй позже.")
        return
    lines = ["🏴‍☠️ <b>Клад на суше России</b>", ""]
    left = max(0.0, entry["expires_ts"] - now)
    days = int(left // 86400)
    hours = int((left % 86400) // 3600)
    lines.append(f"⏳ Клад сгорит через {days} дн {hours} ч (если раньше не найдут).")
    for off, text in entry["hints"]:
        if entry["created_ts"] + off <= now:
            lines.append(text)
    nxt = next((off for off, _ in entry["hints"] if entry["created_ts"] + off > now), None)
    if nxt is not None:
        lines.append(f"…следующая подсказка через {int((entry['created_ts'] + nxt - now) // 3600)} ч")
    # тепло/холодно от позиции моего человечка (только если он уже есть)
    uid = str(update.effective_user.id)
    found = False
    with walker_lock:
        with geo_lock:
            mkey = resolve_marker_key(chat_id, uid, "")
        w = walker_state.get(chat_id, {}).get(mkey) if mkey else None
        if w is not None:
            if walker_progress(w):
                found = klad_on_arrival(chat_id, mkey, w)
            if not found:
                dist = haversine_km(w["lat"], w["lon"], entry["lat"], entry["lon"])
                temp = ("🔥🔥 жгётся" if dist < 300 else "🔥 горячо" if dist < 800
                        else "❄ прохладно" if dist < 1500 else "🥶 холодно")
                lines.append(f"🚶 Твой человечек: ~{max(10, int(round(dist, -2)))} км до клада — {temp}")
    if found:
        await update.message.reply_text(
            "🏴‍☠️ Твой человечек только что ВЫКОПАЛ КЛАД! +10 ☄️ ЗП, +10 💗 и сувенир 🏴‍☠️ "
            "уже в сумке — загляни в «Мой сундук». Новый клад уже зарыт: жди подсказок!")
        return
    await update.message.reply_text("\n".join(lines), parse_mode="HTML",
                                    disable_web_page_preview=True)


async def on_guess(update: Update, context: ContextTypes.DEFAULT_TYPE, guess: str) -> None:
    """Ход в соло-игре: ответ игрока против компьютера (guess — уже разобранный ch-формат)."""
    remember_user(update.effective_user)
    key = (update.message.chat_id, update.effective_user.id)
    game = solo_games.get(key)
    if game is None:
        return  # бот молчит, пока игра не начата командой /startsum

    error = valid_guess(guess)
    if error:
        await update.message.reply_text(error)
        return

    game["attempts"] += 1
    bulls, cows = bulls_and_cows(game["secret"], guess)
    game.setdefault("history", []).append((guess, bulls, cows))
    if bulls == 4:
        st = player_stats(update.effective_user.id)
        st["wins"] += 1
        if st["best"] is None or game["attempts"] < st["best"]:
            st["best"] = game["attempts"]
        mids = game.get("msg_ids", [])
        del solo_games[key]
        msg = await update.message.reply_text(
            f"🎉 Победа! Число {game['secret']} угадано за {game['attempts']} попыток.\nСыграть ещё — /startsum"
        )
        # все ответы бота по игре (и само сообщение о победе) — в чистку через 5 минут
        mids.append(msg.message_id)
        schedule_bc_cleanup(context, update.message.chat_id, mids)
    else:
        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("📜 Мои ходы", callback_data=f"bc_hist:solo:{update.message.chat_id}:{update.effective_user.id}"),
        ]])
        msg = await update.message.reply_text(
            f"{guess} → 🐂 {bulls} · 🐄 {cows} (попытка {game['attempts']})", reply_markup=kb)
        game.setdefault("msg_ids", []).append(msg.message_id)


# ---------- Дуэли Пользователь–Пользователь ----------

async def cmd_play(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/playsum @username — вызвать игрока на дуэль в группе."""
    if not chat_allowed(update.effective_chat):
        return
    remember_user(update.effective_user)
    chat_id = update.message.chat_id
    challenger = update.effective_user

    if update.message.chat.type == "private":
        await update.message.reply_text("Дуэли играются в группе. Добавь меня в группу и вызови там: /playsum @игрок")
        return
    if chat_id in duels:
        await update.message.reply_text("В этом чате уже идёт дуэль. Дождитесь её окончания или /stop.")
        return
    if chat_id in pending_challenges:
        await update.message.reply_text("В этом чате уже есть активный вызов.")
        return

    # сначала пробуем reply на сообщение противника — это работает всегда
    reply_user = None
    if update.message.reply_to_message and update.message.reply_to_message.from_user:
        u = update.message.reply_to_message.from_user
        if not u.is_bot:
            remember_user(u)
            reply_user = u

    opponent_id = None
    if reply_user is not None:
        opponent_id = reply_user.id
    else:
        opponent_id = find_user_id(update.message.text, update.message.entities)
    if opponent_id is None:
        await update.message.reply_text(
            "Не смог определить игрока. Надёжный способ: сделай ответ (reply) на сообщение "
            "противника командой /playsum.\nДругие варианты: /playsum @username (противник должен "
            "был писать в группе, пока я там есть) или /playsum 123456789 (его числовой id)."
        )
        return
    if opponent_id == challenger.id:
        await update.message.reply_text("Нельзя вызвать самого себя 🙂")
        return

    job = context.job_queue.run_once(expire_challenge, CHALLENGE_TTL_SECONDS, chat_id=chat_id)
    pending_challenges[chat_id] = {
        "challenger_id": challenger.id,
        "challenger_name": display_name(challenger),
        "opponent_id": opponent_id,
        "opponent_name": None,  # подставим при принятии, когда увидим пользователя
        "job": job,
    }
    keyboard = InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("✅ Принять", callback_data="duel:accept"),
                InlineKeyboardButton("❌ Отказать", callback_data="duel:decline"),
            ]
        ]
    )
    await update.message.reply_text(
        f"⚔️ {display_name(challenger)} вызывает на дуэль «Быки и коровы»!\n"
        f"Противник должен ответить в течение {CHALLENGE_TTL_SECONDS // 60} минут.",
        reply_markup=keyboard,
    )


async def expire_challenge(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Сгорание вызова по таймауту."""
    chat_id = context.job.chat_id
    if chat_id in pending_challenges:
        del pending_challenges[chat_id]
        try:
            await context.bot.send_message(chat_id, "⌛ Вызов на дуэль истёк. Сыграть заново — /playsum @игрок")
        except BadRequest:
            pass


async def on_challenge_button(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Принятие/отказ на вызов (кнопки под сообщением с вызовом)."""
    if not chat_allowed(update.effective_chat):
        await update.callback_query.answer()
        return
    query = update.callback_query
    remember_user(query.from_user)
    chat_id = query.message.chat_id
    challenge = pending_challenges.get(chat_id)

    if challenge is None:
        await query.answer("Этот вызов уже неактивен.", show_alert=True)
        return
    if query.from_user.id != challenge["opponent_id"]:
        await query.answer("Этот вызов не тебе 🙂", show_alert=True)
        return

    challenge["job"].schedule_removal()
    del pending_challenges[chat_id]

    if query.data == "duel:decline":
        await query.answer("Отказано")
        await query.edit_message_text("❌ Вызов отклонён. Новая попытка — /playsum @игрок")
        return

    await query.answer("Принято!")
    opponent = query.from_user
    challenge["opponent_name"] = display_name(opponent)

    players = {
        challenge["challenger_id"]: {"name": challenge["challenger_name"], "secret": None},
        opponent.id: {"name": challenge["opponent_name"], "secret": None},
    }
    duels[chat_id] = {
        "players": players,
        "order": [challenge["challenger_id"], opponent.id],
        "turn": 0,
        "attempts": {challenge["challenger_id"]: 0, opponent.id: 0},
    }

    # просим числа в личке
    for uid in players:
        try:
            await context.bot.send_message(
                uid,
                f"⚔️ Дуэль «Быки и коровы» в группе!\n"
                f"Загадай своё число из 4 разных цифр (первая — не ноль) командой:\n"
                f"/secret 1234\n"
                f"Число увидит только я — противник его не узнает.",
            )
        except (Forbidden, BadRequest):
            await context.bot.send_message(
                chat_id,
                f"{players[uid]['name']}, мне нужно узнать твоё число в личке: "
                f"открой со мной диалог и нажми /start, затем введи /secret 1234.",
            )
    await query.edit_message_text(
        f"⚔️ Дуэль: {challenge['challenger_name']} против {challenge['opponent_name']}!\n"
        f"Оба игрока загадали числа в личке. Первым ходит {challenge['challenger_name']} — "
        f"пиши в группу 4 цифры."
    )


async def cmd_secret(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/secret 1234 (в личке бота) — загадать число для дуэли."""
    remember_user(update.effective_user)
    if update.message.chat.type != "private":
        return  # команда только в личке
    user = update.effective_user
    text = update.message.text.split(maxsplit=1)
    if len(text) < 2:
        await update.message.reply_text("Формат: /secret 1234")
        return
    guess = text[1].strip()
    error = valid_guess(guess)
    if error:
        await update.message.reply_text(error + " Пример: /secret 1234")
        return

    # находим дуэль, где этому игроку нужно загадать число
    for chat_id, duel in duels.items():
        player = duel["players"].get(user.id)
        if player is not None and player["secret"] is None:
            player["secret"] = guess
            await update.message.reply_text("✅ Число принято. Ждём противника…" )
            if all(p["secret"] is not None for p in duel["players"].values()):
                first = duel["players"][duel["order"][0]]["name"]
                await context.bot.send_message(
                    chat_id,
                    f"⚔️ Всё готово! Игра началась. Первым ходит {first} — пиши 4 цифры.",
                )
            return
    await update.message.reply_text("Сейчас тебе не нужно загадывать число. Дуэль начинается командой /playsum @игрок в группе.")


async def on_duel_guess(update: Update, context: ContextTypes.DEFAULT_TYPE, guess: str) -> None:
    """Ход в активной дуэли (в группе). guess — уже разобранный ch-формат."""
    chat_id = update.message.chat_id
    user = update.effective_user
    duel = duels[chat_id]
    players = duel["players"]

    current_id = duel["order"][duel["turn"]]
    if user.id != current_id:
        await update.message.reply_text(f"Сейчас ход {players[current_id]['name']}.")
        return

    error = valid_guess(guess)
    if error:
        await update.message.reply_text(error)
        return

    opponent_id = duel["order"][1 - duel["turn"]]
    opponent_secret = players[opponent_id]["secret"]
    duel["attempts"][user.id] += 1
    bulls, cows = bulls_and_cows(opponent_secret, guess)
    players[user.id].setdefault("history", []).append((guess, bulls, cows))

    if bulls == 4:
        winner_stats = player_stats(user.id)
        winner_stats["wins"] += 1
        if winner_stats["best"] is None or duel["attempts"][user.id] < winner_stats["best"]:
            winner_stats["best"] = duel["attempts"][user.id]
        loser_id = opponent_id
        mids = duel.get("msg_ids", [])
        del duels[chat_id]
        msg = await update.message.reply_text(
            f"🏆 {players[user.id]['name']} угадал число {opponent_secret} за {duel['attempts'][user.id]} попыток!\n"
            f"Победа! {players[user.id]['name']} : {duel['attempts'][user.id]} — {duel['attempts'][loser_id]} : {players[loser_id]['name']}\n"
            f"Реванш — /playsum @игрок"
        )
        # все ответы бота по дуэли (и само сообщение о победе) — в чистку через 5 минут
        mids.append(msg.message_id)
        schedule_bc_cleanup(context, chat_id, mids)
        return

    duel["turn"] = 1 - duel["turn"]
    next_name = players[duel["order"][duel["turn"]]]["name"]
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("📜 Мои ходы", callback_data=f"bc_hist:duel:{chat_id}:{user.id}"),
    ]])
    msg = await update.message.reply_text(
        f"{players[user.id]['name']}: {guess} → 🐂 {bulls} · 🐄 {cows} (попытка {duel['attempts'][user.id]})\n"
        f"Ход: {next_name}",
        reply_markup=kb,
    )
    duel.setdefault("msg_ids", []).append(msg.message_id)


async def on_bc_history(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Кнопка «📜 Мои ходы» под ответом бота — окошко со всеми названными
    числами игрока за текущую сессию (последний ход сверху, первый внизу)."""
    query = update.callback_query
    _, mode, chat_id_s, user_id_s = query.data.split(":")
    chat_id, user_id = int(chat_id_s), int(user_id_s)
    history = None
    if mode == "solo":
        game = solo_games.get((chat_id, user_id))
        history = game.get("history") if game else None
    else:
        duel = duels.get(chat_id)
        player = duel["players"].get(user_id) if duel else None
        history = player.get("history") if player else None
    if not history:
        await query.answer("📜 История пуста — ходов пока не было.", show_alert=True)
        return
    lines = [f"{guess} → 🐂 {bulls} · 🐄 {cows}" for guess, bulls, cows in reversed(history)]
    header = f"📜 Твои ходы ({len(history)}):"
    text = header + "\n" + "\n".join(lines)
    if len(text) <= 190:  # лимит alert — 200 символов
        await query.answer(text, show_alert=True)
    else:
        # в окошко помещаются первые строки, полный список — сообщением в чат
        await query.answer(header + "\n" + "\n".join(lines[:6]) + "\n… (полный список — в чате)", show_alert=True)
        await context.bot.send_message(chat_id, text)


async def on_saga_chapter(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Глава саги: сообщение «saga <текст>» (префикс регистронезависим)."""
    chat_id = update.message.chat_id
    s = saga_state.get(chat_id)
    if s is None:
        return  # сага не идёт — молчим
    body = update.message.text[len(SAGA_PREFIX):].strip()
    n = len(s["chapters"])
    if len(body) < SAGA_MIN_LEN:
        await update.message.reply_text(
            f"📜 Коротковато — глава от {SAGA_MIN_LEN} символов. Добавь деталей 🙂")
        return
    if len(body) > SAGA_MAX_LEN:
        await update.message.reply_text(
            f"📜 Длинновато — максимум {SAGA_MAX_LEN} символов. Разбей на две главы 🙂")
        return
    if SAGA_END_RE.search(body):
        await update.message.reply_text(
            "📜 Досрочно заканчивать сагу нельзя — история длиннее, чем кажется 🙂")
        return
    if s["last_author"] == update.effective_user.id:
        await update.message.reply_text(
            "📜 Две главы подряд одним автором нельзя — пусть продолжит кто-то другой 🙂")
        return
    s["chapters"].append(body)
    s["last_author"] = update.effective_user.id
    s["last_chapter_ts"] = time.time()
    s["last_nag_ts"] = 0.0
    ac = s.setdefault("author_counts", {})
    au = str(update.effective_user.id)
    ac[au] = ac.get(au, 0) + 1   # для статистики недели: главы по авторам не сохраняются — только счётчик
    saga_save_to_github()
    # политика анонимности: само сообщение с текстом главы стираем из чата
    try:
        await context.bot.delete_message(chat_id, update.message.message_id)
    except Exception as e:
        print(f"[paint_bot] не смог удалить сообщение главы: {e!r}", flush=True)
    n += 1
    if n >= SAGA_MAX_CHAPTERS:
        await update.message.reply_text(f"✅ Глава {n}/{SAGA_MAX_CHAPTERS} принята — сага завершена!")
        await saga_publish(context.bot, chat_id)
    else:
        await update.message.reply_text(f"✅ Глава {n}/{SAGA_MAX_CHAPTERS} принята.")


async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Точка входа: «saga <текст>» — глава саги; ch1234 — ход быков; иначе молчим."""
    if not chat_allowed(update.effective_chat):
        return
    remember_user(update.effective_user)
    record_tgid(update.message.chat_id, update.effective_user)
    text = update.message.text or ""
    if text.lower().startswith(SAGA_PREFIX + " "):
        await on_saga_chapter(update, context)
        return
    guess = parse_ch(update.message.text)
    if guess is None:
        return  # не формат хода — бот молчит

    chat_id = update.message.chat_id
    duel = duels.get(chat_id)
    if duel is not None and update.effective_user.id in duel["players"]:
        await on_duel_guess(update, context, guess)
        return
    await on_guess(update, context, guess)


async def on_my_chat_member(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Бота добавили в группу/канал: если не из белого списка — предупреждение и жалоба админу."""
    member = update.my_chat_member
    chat = member.chat
    if member.new_chat_member.status not in ("member", "administrator"):
        return  # это не добавление (удаление, кик и т.п.)
    if chat_allowed(chat):
        return  # разрешённая группа — всё в порядке
    try:
        await context.bot.send_message(
            chat.id,
            "Бот не может работать в данной группе\\канале. Срочно удалите его.",
        )
    except Exception as e:
        print(f"[paint_bot] не смог предупредить чат {chat.id}: {e!r}", flush=True)
    # у объекта Chat нет invite_link — только @username для публичных групп
    link = f"@{chat.username}" if getattr(chat, "username", None) else "нет публичной ссылки"
    try:
        await context.bot.send_message(
            ADMIN_ID,
            f"⚠️ Бота добавили в неразрешённый чат!\n"
            f"Название: {chat.title}\n"
            f"Ссылка: {link}\n"
            f"ID чата: {chat.id}",
        )
    except Exception as e:
        # админ не открывал бота или неверный ADMIN_ID — ошибка видна в логах Render
        print(f"[paint_bot] не смог уведомить админа {ADMIN_ID}: {e!r}", flush=True)


def seed_sandbox_test_markers() -> None:
    """Бета Песочницы: метки Тест2 (Тюмень, управляет Sumai через персону) и Тест3 (Казахстан, без доступа)."""
    markers = geo_state.setdefault(GEO2_CHAT_ID, {})
    added = False
    for user, name, icon, lat, lon in (
        ("test2", "Тест2", "🦖", 57.152, 65.528),
        ("test3", "Тест3", "🦄", 48.0, 66.9),
    ):
        if user not in markers:
            markers[user] = {"user": user, "name": name, "icon": icon,
                             "lat": lat, "lon": lon, "got": 0, "read": 0}
            added = True
    if added:
        geo_save_to_github()
        print("[paint_bot] geo: засеяны тестовые метки Тест2/Тест3 для Песочницы", flush=True)


# ---------- Анонимные сообщения: релей из ЛС в чат «Другое измерение» ----------
ANON_GROUP_ID = -1002304715333
ANON_INTERVAL_SEC = 30          # минимальный интервал между анонимными отправками
ANON_ADMINS = {769828689, 1217843099, 8584582199, 8668538137}  # кто может /anonstop и /anonstart
ANON_MEMBER_CACHE_SEC = 600
ANON_PREFIX_HTML = ('<blockquote>🕶️ Пользователь чата отправил '
                    'анонимное сообщение:</blockquote>')
# Telegram не даёт менять размер/цвет шрифта: blockquote — самый «блеклый» вариант оформления
anon_mode = set()        # uid, у кого включён режим
anon_blocked = False     # глобальная блокировка (/anonstop)
anon_last = {}           # uid -> ts последней успешной отправки
anon_member_cache = {}   # uid -> (ts, is_member)


def anon_is_member(user_id: int) -> bool:
    """Участник (или админ) группы «Другое измерение»? Кэш на 10 минут."""
    now = time.time()
    hit = anon_member_cache.get(user_id)
    if hit and now - hit[0] < ANON_MEMBER_CACHE_SEC:
        return hit[1]
    ok = False
    try:
        url = (f"https://api.telegram.org/bot{BOT_TOKEN}/getChatMember"
               f"?chat_id={ANON_GROUP_ID}&user_id={user_id}")
        data = json.load(urllib.request.urlopen(url, timeout=15))
        st = (data.get("result") or {}).get("status", "")
        ok = st in ("member", "administrator", "creator")
    except Exception as e:
        print(f"[anon] getChatMember uid={user_id} ошибка: {e!r}", flush=True)
    anon_member_cache[user_id] = (now, ok)
    return ok


async def anon_report_admin(bot, foreign_user, extra=""):
    """ЛС админу: кто-то чужой ломится в бота."""
    try:
        await bot.send_message(
            ADMIN_ID,
            "\U0001F6AB Чужой пользователь пытался использовать бота\n"
            f"ID: {foreign_user.id}\n"
            f"Юзернейм: @{foreign_user.username or '—'}\n"
            f"Имя: {foreign_user.full_name}\n" + extra)
    except Exception as e:
        print(f"[anon] не смог уведомить админа: {e!r}", flush=True)


async def cmd_anon_on(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/anonON (только ЛС): включить режим анонимных сообщений."""
    if update.effective_chat.type != "private":
        await update.message.reply_text("Анонимный режим включается только в личке с ботом 🙂")
        return
    user = update.effective_user
    if anon_blocked:
        await update.message.reply_text("Режим заблокирован Администратором Чата")
        return
    if not anon_is_member(user.id):
        await update.message.reply_text(
            "У вас нет доступа к командам Бота. Прекратите его использование")
        await anon_report_admin(context.bot, user, extra="Команда: /anonON\n")
        return
    anon_mode.add(user.id)
    await update.message.reply_text(
        "\U0001F576️ Режим анонимных сообщений ВКЛЮЧЁН.\n"
        "Всё, что ты напишешь мне в ЛС (текст, фото, видео, голосовые, кружки, стикеры), "
        "будет отправлено в чат «Другое измерение» от моего имени.\n"
        "Интервал между отправками — 30 секунд. Выключить: /anonOFF")


async def cmd_anon_off(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/anonOFF (только ЛС): выключить режим."""
    if update.effective_chat.type != "private":
        return
    anon_mode.discard(update.effective_user.id)
    anon_last.pop(update.effective_user.id, None)
    await update.message.reply_text("\U0001F576️ Режим анонимных сообщений выключен.")


async def cmd_anon_stop(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/anonstop (в группе, только для ANON_ADMINS): полная блокировка режима."""
    global anon_blocked
    if update.effective_chat.id != ANON_GROUP_ID or update.effective_user.id not in ANON_ADMINS:
        return
    anon_blocked = True
    anon_mode.clear()
    await update.message.reply_text(
        "\U0001F576️ Анонимный режим ЗАБЛОКИРОВАН администратором. Активные сессии сброшены.")


async def cmd_anon_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/anonstart (в группе, только для ANON_ADMINS): разблокировка режима."""
    global anon_blocked
    if update.effective_chat.id != ANON_GROUP_ID or update.effective_user.id not in ANON_ADMINS:
        return
    anon_blocked = False
    await update.message.reply_text("\U0001F576️ Анонимный режим разблокирован.")


async def on_anon_dm(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """ЛС с ботом: релей анонимных сообщений в «Другое измерение» (block=False — не мешает другим играм)."""
    msg = update.effective_message
    user = update.effective_user
    if user is None or msg is None:
        return
    if user.id not in anon_mode:
        return
    if anon_blocked:
        await msg.reply_text("Режим заблокирован Администратором Чата")
        return
    now = time.time()
    left = ANON_INTERVAL_SEC - (now - anon_last.get(user.id, 0.0))
    if left > 0:
        await msg.reply_text(
            f"⏳ До следующей отправки анонимного сообщения осталось {int(left) + 1} сек.")
        return
    try:
        if msg.text:
            await context.bot.send_message(
                ANON_GROUP_ID,
                ANON_PREFIX_HTML + "\n\n" + f"<i>{html.escape(msg.text)}</i>",
                parse_mode="HTML")
        elif msg.caption is not None:
            await context.bot.copy_message(chat_id=ANON_GROUP_ID, from_chat_id=msg.chat_id,
                                           message_id=msg.message_id,
                                           caption=ANON_PREFIX_HTML + "\n\n" + f"<i>{html.escape(msg.caption)}</i>",
                                           parse_mode="HTML")
        else:
            await context.bot.copy_message(chat_id=ANON_GROUP_ID, from_chat_id=msg.chat_id,
                                           message_id=msg.message_id)
        anon_last[user.id] = time.time()
        kind = "text" if msg.text else "media"
        preview = (msg.text or msg.caption or "")[:100]
        print(f"[anon] uid={user.id} @{user.username or '-'} name={user.full_name!r} "
              f"kind={kind} {preview!r}", flush=True)
        await msg.reply_text("✅ Анонимно отправлено в «Другое измерение».")
    except Exception as e:
        print(f"[anon] ошибка отправки uid={user.id}: {e!r}", flush=True)
        await msg.reply_text("⚠️ Не получилось отправить — попробуй ещё раз.")


GEO2_ANNOUNCE_FLAG = "geo2_release_announced.txt"  # флаг в data-репо: анонс релиза GEO2 отправлен


async def announce_geo2_release_job(context) -> None:
    """Одноразовый анонс GEO2 в чаты бета-теста. Флаг в data-репо не даёт повторить при рестарте."""
    try:
        urllib.request.urlopen(geo_github_request("GET", GEO2_ANNOUNCE_FLAG), timeout=15)
        context.job.schedule_removal()  # анонс уже был — задача больше не нужна
        return
    except urllib.error.HTTPError as e:
        if e.code != 404:
            print(f"[paint_bot] анонс GEO2: флаг проверить не вышло: {e!r}", flush=True)
            return  # временная ошибка — повторим на следующем тике
    except Exception as e:
        print(f"[paint_bot] анонс GEO2: флаг проверить не вышло: {e!r}", flush=True)
        return
    text = (
        "🌍✨ Друзья, привет!\n\n"
        "Для вас полностью переработан интерфейс «ГеографииЧата» — теперь это удобная "
        "панель инструментов сбоку, тёмная тема, «Мой сундук» с вашими сокровищами, "
        "красивые окна и плавная карта. Все ваши метки, письма, подарки и события — на месте.\n\n"
        "Посмотреть можно прямо сейчас — жмите «Открыть карту» 👇"
    )
    sent = 0
    for cid in (GEO2_CHAT_ID, ANON_GROUP_ID):
        try:
            await context.bot.send_message(cid, text, reply_markup=geo2_keyboard(cid))
            sent += 1
        except Exception as e:
            print(f"[paint_bot] анонс GEO2 в чат {cid} не ушёл: {e!r}", flush=True)
    if sent == 0:
        return  # ни в один чат не дошло — флаг не ставим, повторим через 2 мин
    try:
        body = {"content": base64.b64encode("2026-11-01".encode("utf-8")).decode("ascii")}
        try:
            current = json.load(urllib.request.urlopen(
                geo_github_request("GET", GEO2_ANNOUNCE_FLAG), timeout=15))
            body["sha"] = current["sha"]
        except urllib.error.HTTPError as e:
            if e.code != 404:
                raise
        req = geo_github_request("PUT", GEO2_ANNOUNCE_FLAG,
                               {"Content-Type": "application/json"})
        req.data = json.dumps({**body, "message": "geo2 release announced"}).encode("utf-8")
        urllib.request.urlopen(req, timeout=15)
        print("[paint_bot] анонс GEO2 отправлен, флаг в data-репо выставлен", flush=True)
    except Exception as e:
        print(f"[paint_bot] анонс GEO2 ушёл, но флаг не записался: {e!r}", flush=True)
    context.job.schedule_removal()


def geo_sweep_job(context=None) -> None:
    """Фоновый прогон «ленивого» осмотра активных чатов: прибытия писем/подарков/какашек,
    перелёты самолёта, замена неявившегося капитана — уведомления уходят по расписанию,
    а не пачкой при входе первого игрока. Идём по тому же коду /geodata по localhost
    (viewer пустой — никаких tid-меток не ставится, только чат-уровень событий).
    context — обязательный аргумент job_queue; не используется."""
    port = int(os.environ.get("PORT", "10000"))
    chats = set(geo_state.keys())
    for st in (letters_state, poops_state, gifts_state, islands_state,
               ships_state, wrecks_state):
        for v in st.values():
            c = v.get("chat")
            if c:
                chats.add(c)
    for d in ship_duels.values():
        c = d.get("chat")
        if c:
            chats.add(c)
    for cid in sorted(chats):
        try:
            urllib.request.urlopen(
                f"http://127.0.0.1:{port}/geodata?chat={cid}&user=&name=", timeout=15)
        except Exception as e:
            print(f"[paint_bot] sweep чат {cid}: {e!r}", flush=True)


def main() -> None:
    # Поднимаем сохранённые метки географии, письма и вулканы из GitHub (после перезапусков)
    geo_load_from_github()
    seed_sandbox_test_markers()
    letters_load_from_github()
    volcano_load_from_github()
    saga_load_from_github()
    meteor_load_from_github()
    submarine_load_from_github()
    islands_load_from_github()
    sifa_load_from_github()
    walker_load_from_github()
    klad_load_from_github()
    ships_load_from_github()
    wrecks_load_from_github()
    duels_load_from_github()
    market_load_from_github()
    tgids_load_from_github()
    apply_marker_bindings()
    apply_tid_bindings()
    apply_remove_tid_dup_markers()
    apply_sandbox_grants()
    apply_sandbox_island_levels()
    apply_ship_teleport_sumai()
    apply_ship_teleport_sumai_random_ocean()
    apply_sumai_wreck_east6000()
    apply_free_ships_main()
    apply_restore_wrecks()
    apply_fix_mari_pm_duel()
    apply_pm_ship_wins()
    apply_gaya_lyubertsy()
    apply_anon_rename_dasha()
    apply_tatev_coowner()
    apply_andrey_island_rename()
    apply_walker_reloc_2026_11_09()
    # Запускаем HTTP-сервер (проверка живости + холст рисовалки) в отдельном потоке
    threading.Thread(target=run_http_server, daemon=True).start()

    app = Application.builder().token(BOT_TOKEN).build()
    app.add_handler(CommandHandler("startsum", cmd_start))
    app.add_handler(CommandHandler("playsum", cmd_play))
    app.add_handler(CommandHandler("secret", cmd_secret))
    app.add_handler(CommandHandler("stop", cmd_stop))
    app.add_handler(CommandHandler("stats", cmd_stats))
    app.add_handler(CommandHandler("klad", cmd_klad))
    app.add_handler(CommandHandler("helpsum", cmd_help))
    app.add_handler(CommandHandler("myid", cmd_myid))
    app.add_handler(CommandHandler("geo2", cmd_geo2))
    app.add_handler(CommandHandler("delpointgeo", cmd_delpointgeo))
    app.add_handler(CallbackQueryHandler(on_game_menu, pattern="^game:"))
    app.add_handler(CallbackQueryHandler(on_saga_action, pattern="^saga:"))
    app.add_handler(CallbackQueryHandler(on_challenge_button, pattern="^duel:"))
    app.add_handler(CallbackQueryHandler(on_paint_wait, pattern="^paint_wait$"))
    app.add_handler(CallbackQueryHandler(on_stop_choice, pattern="^stop:"))
    app.add_handler(CallbackQueryHandler(on_bc_history, pattern="^bc_hist:"))
    app.add_handler(ChatMemberHandler(on_my_chat_member, chat_member_types=ChatMemberHandler.MY_CHAT_MEMBER))
    app.add_handler(CommandHandler(["anonON", "anonon"], cmd_anon_on))
    app.add_handler(CommandHandler(["anonOFF", "anonoff"], cmd_anon_off))
    app.add_handler(CommandHandler(["anonstop", "anonStop"], cmd_anon_stop))
    app.add_handler(CommandHandler(["anonstart", "anonStart"], cmd_anon_start))
    # анонимный режим: ЛС с ботом -> «Другое измерение» (block=False — не перебивает другие игры)
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE & ~filters.COMMAND, on_anon_dm, block=False))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.job_queue.run_repeating(process_paint_updates, interval=1.0)
    app.job_queue.run_repeating(paint_periodic_sweep, interval=15.0)
    # автобэкап меток и писем: каждый день в 01:00 по Москве
    app.job_queue.run_daily(backup_job, time=datetime.time(1, 0, tzinfo=MSK_TZ))
    # итоги недели: каждую пятницу в 16:00 по Москве в «Другое измерение» (не удаляются)
    app.job_queue.run_daily(weekly_stats_job, time=datetime.time(16, 0, tzinfo=MSK_TZ),
                            days=(4,))
    # вулканы: фоновый спавн + уведомление в чат при появлении
    app.job_queue.run_repeating(volcano_spawn_job, interval=60.0, first=10.0)
    # метеориты: фоновое падение + уведомление в чат
    app.job_queue.run_repeating(meteor_fall_job, interval=60.0, first=20.0)
    # сифа: чистка неактивных касаток (48ч) + ротация Сифы (8ч) + уведомление
    app.job_queue.run_repeating(sifa_sweep_job, interval=600.0, first=60.0)
    # одноразовый анонс релиза GEO2 (самоотключается после отправки)
    app.job_queue.run_repeating(announce_geo2_release_job, interval=120.0, first=15.0)
    # подводные лодки: фоновый спавн в океанах БЕЗ уведомления в чат
    app.job_queue.run_repeating(submarine_spawn_job, interval=60.0, first=30.0)
    # ленивый осмотр ГЕО: уведомления о прибытиях/перелётах уходят по расписанию
    app.job_queue.run_repeating(geo_sweep_job, interval=60.0, first=45.0)
    # сага: слезливое напоминание, если 8ч никто не пишет главу (сага не начата — молчим)
    app.job_queue.run_repeating(saga_nag_job, interval=1800.0, first=120.0)
    # клад: сгорел (7 дней) — новый; появилась подсказка (каждые 12 ч) — анонс в чат
    app.job_queue.run_repeating(klad_sweep_job, interval=3600.0, first=300.0)
    app.run_polling()


if __name__ == "__main__":
    main()
