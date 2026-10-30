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
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs
import urllib.error
import urllib.request

from PIL import Image
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, InputMediaPhoto, MessageEntity, Update, WebAppInfo
from telegram.error import BadRequest, Forbidden
from telegram.ext import Application, CallbackQueryHandler, ChatMemberHandler, CommandHandler, ContextTypes, MessageHandler, filters

# Токен бота берётся из переменной окружения BOT_TOKEN (задаётся в панели Render)
BOT_TOKEN = os.environ["BOT_TOKEN"]

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
LETTER_FAST_SENDERS = {"Андрюха": 2.0}
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
METEOR_FILE = "meteor.json"
METEOR_LIFETIME_SEC = 300     # 5 минут на сбор пыли из свежей воронки
METEOR_PERIOD_SEC = 3600      # перерыв между падениями — час (+ случайные 0–50 мин)
LETTER_BOOST_KM = 1000        # ускорение: мгновенное продвижение письма на 1000 км, стакается

METEOR_NOTIFY_TEXT = ("☄️ МЕТЕОРИТ! На карту чата упал метеорит — спеши собрать "
                      "ресурс ЗвезднаяПыль! Открой карту, найди воронку 💥 и жми "
                      "«Забрать ЗП» — кто первый, тому и пыль. Пыль нужна, чтобы "
                      "ускорять письма ✉️⏩")


def meteor_save_to_github() -> None:
    payload = {"meteors": {str(k): v for k, v in meteor_state.items()},
               "stardust": stardust_state}
    _save_json_to_github(METEOR_FILE, payload, geo_lock, "meteor")


def meteor_load_from_github() -> None:
    loaded = _load_json_from_github(METEOR_FILE, "meteor")
    if not loaded:
        return
    meteor_state.update({int(cid): m for cid, m in loaded.get("meteors", {}).items()})
    stardust_state.update(loaded.get("stardust", {}))
    print(f"[paint_bot] meteor: чатов {len(meteor_state)}, балансов пыли {len(stardust_state)}", flush=True)


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


def island_of(chat_id: int, user: str):
    """Остров чата, где user — владелец (основной или совладелец), или None."""
    for isl in islands_state.values():
        if isl["chat"] != chat_id or isl.get("banned"):
            continue
        owners = isl.get("owners") or [isl["owner"]]
        if user in owners:
            return isl
    return None


def stardust_get(chat_id: int, user: str) -> int:
    return stardust_state.get(f"{chat_id}|{user}", 0)


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
        # окно сбора закрылось: воронка остаётся на карте навсегда
        m["craters"].append({"lat": cur["lat"], "lon": cur["lon"],
                             "fall_ts": cur["fall_ts"], "zp": 1 if cur["taken"] else 0})
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


def tg_send_message_id(chat_id: int, text: str):
    """Отправить сообщение и вернуть message_id (None при ошибке)."""
    try:
        req = urllib.request.Request(
            f"https://api.telegram.org/bot{BOT_TOKEN}/sendMessage",
            data=json.dumps({"chat_id": chat_id, "text": text}).encode("utf-8"),
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


def tg_send_with_cleanup(chat_id: int, text: str, ttl_sec: int) -> None:
    """Отправить уведомление и автоудалить его через ttl_sec (из HTTP-потока)."""
    msg_id = tg_send_message_id(chat_id, text)
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

GEO2_HTML_PAGE = """<!DOCTYPE html>
<!-- build:2026-10-30-1422 -->
<html lang="ru">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, user-scalable=no">
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css">
<script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script>
<style>
  :root {
    --bg: var(--tg-theme-bg-color, #0f1720);
    --card: var(--tg-theme-secondary-bg-color, #1a2634);
    --text: var(--tg-theme-text-color, #eef3f8);
    --hint: var(--tg-theme-hint-color, #8a99ab);
    --accent: var(--tg-theme-button-color, #2ea6ff);
    --accent-text: var(--tg-theme-button-text-color, #ffffff);
  }
  * { box-sizing: border-box; }
  body { margin:0; font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,sans-serif;
    background:var(--bg); color:var(--text); }
  #map { width:100%; height:64vh; border-radius:0 0 18px 18px; }
  .bar { padding:8px; display:flex; flex-wrap:wrap; gap:6px; align-items:center; background:var(--card); }
  input { flex:1; min-width:140px; padding:10px; border-radius:12px;
    border:1px solid rgba(140,160,180,.25); font-size:15px; background:var(--bg); color:var(--text); }
  input:focus { outline:none; border-color:var(--accent); }
  button { padding:10px 14px; border-radius:12px; border:none; font-size:15px;
    background:var(--accent); color:var(--accent-text); cursor:pointer;
    transition:transform .12s ease, opacity .12s ease, background .12s ease; }
  button:active { transform:scale(.95); opacity:.85; }
  #status { position:fixed; left:50%; bottom:18px; transform:translateX(-50%) translateY(10px);
    max-width:92vw; padding:10px 16px; border-radius:14px; background:rgba(15,23,32,.94);
    color:#eef3f8; font-size:14px; opacity:0; transition:opacity .25s ease, transform .25s ease;
    pointer-events:none; z-index:2000; box-shadow:0 6px 24px rgba(0,0,0,.4); }
  #status.show { opacity:1; transform:translateX(-50%) translateY(0); }
  .an { font-size:24px; background:var(--bg); border:2px solid rgba(140,160,180,.25);
    border-radius:12px; padding:4px 8px; cursor:pointer;
    transition:transform .12s ease, border-color .12s ease, background .12s ease; }
  .an.on { border-color:var(--accent); background:rgba(46,166,255,.18); transform:scale(1.12); }
  .emoji-marker { background:none; border:none; }
  /* появление маркеров */
  .mk { animation:mkpop .35s cubic-bezier(.34,1.56,.64,1); }
  @keyframes mkpop { from { transform:scale(0); } to { transform:scale(1); } }
  /* пульс событий (вулкан, кит) */
  .mk-pulse { position:relative; }
  .mk-pulse::after { content:''; position:absolute; inset:-6px; border-radius:50%;
    border:3px solid rgba(255,105,58,.85); animation:mkrings 1.7s ease-out infinite; }
  @keyframes mkrings { from { transform:scale(.55); opacity:1; } to { transform:scale(1.6); opacity:0; } }
  /* бренд-чип на карте */
  .brand { position:absolute; top:10px; left:10px; z-index:1000; display:flex;
    align-items:baseline; gap:6px; padding:6px 12px; border-radius:999px;
    background:rgba(15,23,32,.85); color:#eef3f8; font-size:14px;
    backdrop-filter:blur(6px); box-shadow:0 2px 10px rgba(0,0,0,.3); pointer-events:none; }
  .brand b { color:#7ec8ff; }
  .brand span { font-size:11px; color:#8a99ab; }
  /* карточки попапов Leaflet */
  .leaflet-popup-content-wrapper { border-radius:16px; background:var(--card);
    color:var(--text); box-shadow:0 10px 32px rgba(0,0,0,.45); }
  .leaflet-popup-content { margin:12px 16px; font-size:14px; line-height:1.5; }
  .leaflet-popup-content button { margin:2px 2px 0 0; padding:7px 10px; font-size:13px; }
  .leaflet-popup-tip { background:var(--card); }
  .leaflet-popup-close-button { color:var(--hint) !important; font-size:18px !important;
    padding:7px 9px 0 0 !important; }
  .leaflet-container { font:inherit; }
  .leaflet-bar a { background:var(--card); color:var(--text); border-bottom:1px solid rgba(140,160,180,.2); }
</style>
</head>
<body>
<div id="map"><div class="brand">🌍 ГеографияЧата <b>2.0</b> <span>бета · Песочница</span></div></div>
<div class="bar" id="animals"></div>
<div class="bar">
  <input id="name" placeholder="Твоё имя" maxlength="24">
  <button id="delBtn" title="Удалить мою метку" style="display:none;background:#c0392b;">🗑</button>
  <button id="saveBtn">📍 Поставить метку</button>
  <button id="distBtn" style="background:#888;">📏 Расстояние</button>
  <button id="letterBtn" style="background:#888;">✉️ Письмо</button>
  <button id="islandBuyBtn" style="background:#888;">🏝️ Купить остров</button>
  <button id="personaBtn" style="display:none;background:#8e44ad;">🎭 Тест2</button>
  <button id="volcanoBtn" style="display:none;background:#e05a3a;" title="Вызвать вулкан">🌋</button>
  <button id="meteorBtn" style="display:none;background:#5b7cfa;" title="Вызвать метеорит">☄️</button>
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
  const statusEl = document.getElementById('status');
  let statusTimer = null;
  const status = t => {
    statusEl.textContent = t;
    statusEl.classList.add('show');
    clearTimeout(statusTimer);
    statusTimer = setTimeout(() => statusEl.classList.remove('show'), 2600);
  };
  const escapeHtml = s => { const d = document.createElement('div'); d.textContent = s; return d.innerHTML; };

  const tgUser = (tg.initDataUnsafe && tg.initDataUnsafe.user) || null;
  const nameInput = document.getElementById('name');
  nameInput.value = localStorage.getItem('geo_name')
    || (tgUser && (tgUser.username ? '@' + tgUser.username : tgUser.first_name)) || '';
  const realUserKey = () => String((tgUser && tgUser.id) || nameInput.value.trim() || 'anon');
  const realUserName = () => (tgUser && (tgUser.username ? '@' + tgUser.username : tgUser.first_name))
    || nameInput.value.trim() || 'Аноним';
  let persona = null;  // бета: Sumai действует на карте как Тест2
  const userKey = () => persona ? persona.user : realUserKey();
  const userName = () => persona ? persona.name : realUserName();
  // ===== бета Песочницы: персона Тест2 и ручной спавн событий (только Sumai) =====
  const isSumaiBeta = realUserKey() === 'Sumai'
    || (tgUser && tgUser.username === 'Sumai')
    || nameInput.value.trim() === 'Sumai';
  if (isSumaiBeta) {
    document.getElementById('personaBtn').style.display = '';
    document.getElementById('volcanoBtn').style.display = '';
    document.getElementById('meteorBtn').style.display = '';
  }
  document.getElementById('personaBtn').onclick = () => {
    persona = persona ? null : {user: 'test2', name: 'Тест2'};
    const b = document.getElementById('personaBtn');
    b.textContent = persona ? '🎭 Снова Sumai' : '🎭 Тест2';
    b.style.background = persona ? '#27ae60' : '#8e44ad';
    status(persona ? '🎭 Действуешь как Тест2 (метка у Тюмени)' : '🎭 Снова ты — Sumai');
    load();
  };
  async function spawnEvent(kind) {
    const r = await fetch('/spawnevent', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: userKey(), kind: kind})
    });
    const data = await r.json().catch(() => ({}));
    if (r.ok) {
      status(kind === 'volcano' ? '🌋 Вулкан извергается — ищи на карте!' : '☄️ Метеорит упал — спеши собрать ЗП!');
      load();
    } else {
      status('⚠️ ' + (data.error || 'не вышло вызвать событие'));
    }
  }
  document.getElementById('volcanoBtn').onclick = () => spawnEvent('volcano');
  document.getElementById('meteorBtn').onclick = () => spawnEvent('meteor');

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
      html: '<div class="mk" style="font-size:28px;line-height:1;filter:drop-shadow(0 1px 2px rgba(0,0,0,.4))">' + emoji + '</div>',
      className: 'emoji-marker',
      iconSize: [36, 36], iconAnchor: [18, 18], popupAnchor: [0, -14],
    });
  }

  function renderMarker(m) {
    const emoji = m.icon || '📍';
    const mk = L.marker([m.lat, m.lon], {icon: animalIcon(emoji)}).addTo(map);
    let html = '<span style="font-size:22px">' + emoji + '</span> <b>' + escapeHtml(m.name) + '</b><br>'
      + m.lat.toFixed(3) + ', ' + m.lon.toFixed(3);
    // приблизительное локальное время у метки относительно Москвы (15° долготы = 1 час)
    const tzShift = Math.round((m.lon - 37.6173) / 15);
    const tLocal = new Date(Date.now() + (3 + tzShift) * 3600000);
    const hh = String(tLocal.getUTCHours()).padStart(2, '0');
    const mm = String(tLocal.getUTCMinutes()).padStart(2, '0');
    const tzLabel = 'МСК' + (tzShift >= 0 ? '+' : '−') + Math.abs(tzShift);
    html += '<br>🕒 ' + hh + ':' + mm + ' (' + tzLabel + ')';
    if (m.poops && m.user !== userKey()) html += '<br>💩 розовых какашек: ' + m.poops;
    if (m.gift_pics && m.gift_pics.length) html += '<br>🎁 подарки: ' + m.gift_pics.join(' ');
    if (m.souvenirs && m.souvenirs.length) html += '<br>🏝️ сувениры: ' + m.souvenirs.join(' ');
    if (m.user === userKey()) {
      const got = m.got || 0, read = m.read || 0;
      html += '<br><i>📮 письма — в Почтовом Ящике рядом с меткой</i>'
        + '<br>📬 получено ' + got + ' • прочитано ' + read + ' • непрочитано ' + (got - read)
        + '<br><br>☄️ моя ЗвезднаяПыль: <b>' + (m.zp || 0) + '</b>'
        + '<br>💩 мои Какашки: <b>' + (m.poops || 0) + '</b>';
      const myIsl = (lastIslands || []).find(i => (i.owners || [i.owner]).indexOf(userKey()) >= 0);
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
      html: '<div class="mk" style="font-size:26px;line-height:1;filter:drop-shadow(0 1px 2px rgba(0,0,0,.45))">'
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
      body: JSON.stringify({chat: chat, user: userKey(), id: id})
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
      html: '<div class="mk" style="font-size:26px;line-height:1;filter:drop-shadow(0 1px 2px rgba(0,0,0,.45))">'
        + (full ? '📬' : '📭') + '</div>',
      className: 'emoji-marker',
      iconSize: [34, 34], iconAnchor: [17, 17], popupAnchor: [0, -14],
    });
  }
  function renderMailbox(markersData) {
    if (mailboxMarker) { map.removeLayer(mailboxMarker); mailboxMarker = null; }
    const me = (markersData || []).find(m => m.user === userKey());
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
    if (data.from_id && data.from_id !== userKey()) {
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
      body: JSON.stringify({chat: chat, user: userKey(), name: userName(),
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
      html: '<div class="mk mk-pulse" style="font-size:84px;line-height:1;filter:drop-shadow(0 2px 4px rgba(0,0,0,.5))">🌋</div>',
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
    if (m.user === userKey()) { status('Выбери метку ДРУГОГО участника, а не свою 🙂'); return; }
    const r = await fetch('/volcano', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: userKey(), to_user: m.user})
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
      html: '<div class="mk" style="font-size:26px;line-height:1;background:#ffb6d5;border:2px solid #ff69b4;'
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
      mk.bindPopup('💩 Розовая Какашка в пути… (адресат: *****)');
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
      html: '<div class="mk mk-pulse" style="font-size:60px;line-height:1;filter:drop-shadow(0 2px 3px rgba(0,0,0,.5))">🐳</div>',
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
    if (m.user === userKey()) { status('Выбери метку ДРУГОГО участника, а не свою 🙂'); return; }
    const r = await fetch('/subgift', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: userKey(), name: userName(), to_user: m.user})
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
      html: '<div class="mk" style="font-size:26px;line-height:1;background:#ffe0b3;border:2px solid #ff9d4d;'
        + 'border-radius:50%;padding:3px;filter:drop-shadow(0 1px 2px rgba(0,0,0,.45))">🎁</div>',
      className: 'emoji-marker',
      iconSize: [40, 40], iconAnchor: [20, 52], popupAnchor: [0, -52],
    });
  }
  function renderGift(g) {
    const mk = L.marker([g.lat, g.lon], {icon: giftIcon()}).addTo(map);
    if (!g.arrived) {
      // до доставки адресат неизвестен никому — даже самому адресату (как у какашек)
      mk.bindPopup('🎁 Подарок в пути… (адресат: *****)');
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
      body: JSON.stringify({chat: chat, user: userKey(), id: id})
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
      html: '<div class="mk" style="font-size:28px;line-height:1;filter:drop-shadow(0 1px 2px rgba(0,0,0,.5))">💥</div>',
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
      body: JSON.stringify({chat: chat, user: userKey()})
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
      body: JSON.stringify({chat: chat, user: userKey(), id: id})
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
      html: '<div class="mk" style="font-size:56px;line-height:1;filter:drop-shadow(0 2px 3px rgba(0,0,0,.5))">🏝️</div>',
      className: 'emoji-marker',
      iconSize: [72, 72], iconAnchor: [36, 36], popupAnchor: [0, -40],
    });
  }
  function planeIcon() {
    return L.divIcon({
      html: '<div class="mk" style="font-size:30px;line-height:1;filter:drop-shadow(0 1px 2px rgba(0,0,0,.5))">✈️</div>',
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
    if (isl.guest && isl.guest.user === userKey() && isl.guest.leg === 'staying') {
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
      body: JSON.stringify({chat: chat, user: userKey(), name: userName()})
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
    const others = (lastMarkers || []).filter(xm => xm.user !== userKey());
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
    if (m.user === userKey()) { status('Выбери метку ДРУГОГО участника, а не свою 🙂'); return; }
    const r = await fetch('/islandinvite', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: userKey(), to_user: m.user})
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
      body: JSON.stringify({chat: chat, user: userKey()})
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
      body: JSON.stringify({chat: chat, user: userKey(), building: bid})
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
      body: JSON.stringify({chat: chat, user: userKey()})
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
      body: JSON.stringify({chat: chat, user: userKey()})
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
    if (m.user === userKey()) { status('Выбери метку ДРУГОГО участника, а не свою 🙂'); return; }
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
      body: JSON.stringify({chat: chat, user: userKey(), name: userName(),
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
    const mine = !!markers[userKey()];
    document.getElementById('animals').style.display = mine ? 'none' : 'flex';
    document.getElementById('saveBtn').style.display = mine ? 'none' : '';
    document.getElementById('delBtn').style.display = mine ? '' : 'none';
    nameInput.disabled = mine;
    nameInput.title = mine ? 'Имя закреплено за твоей меткой. Удали метку (🗑 справа), чтобы изменить.' : '';
  }

  async function load() {
    const r = await fetch('/geodata?chat=' + chat + '&user=' + encodeURIComponent(userKey()) + '&t=' + Date.now());
    const data = await r.json();
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
      const haveIsl = lastIslands.some(i => (i.owners || [i.owner]).indexOf(userKey()) >= 0);
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
      + flyingLetters + ' • ☄️ ЗП: ' + (data.stardust || 0)
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
    if (markers[userKey()]) {
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
      body: JSON.stringify({chat: chat, user: userKey(), name: userName(), icon: curIcon,
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
      body: JSON.stringify({chat: chat, user: userKey()})
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


# ---------- Страница «География чата» (Leaflet + OpenStreetMap) ----------

BUILD_TAG = "2026-10-30-1422"  # менять при каждом деплое — диагностика, что на Render свежий код

GEO_HTML_PAGE = """<!DOCTYPE html>
<!-- build:2026-10-30-1422 -->
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
  const userKey = () => String((tgUser && tgUser.id) || nameInput.value.trim() || 'anon');
  const userName = () => (tgUser && (tgUser.username ? '@' + tgUser.username : tgUser.first_name))
    || nameInput.value.trim() || 'Аноним';

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
    // приблизительное локальное время у метки относительно Москвы (15° долготы = 1 час)
    const tzShift = Math.round((m.lon - 37.6173) / 15);
    const tLocal = new Date(Date.now() + (3 + tzShift) * 3600000);
    const hh = String(tLocal.getUTCHours()).padStart(2, '0');
    const mm = String(tLocal.getUTCMinutes()).padStart(2, '0');
    const tzLabel = 'МСК' + (tzShift >= 0 ? '+' : '−') + Math.abs(tzShift);
    html += '<br>🕒 ' + hh + ':' + mm + ' (' + tzLabel + ')';
    if (m.poops && m.user !== userKey()) html += '<br>💩 розовых какашек: ' + m.poops;
    if (m.gift_pics && m.gift_pics.length) html += '<br>🎁 подарки: ' + m.gift_pics.join(' ');
    if (m.souvenirs && m.souvenirs.length) html += '<br>🏝️ сувениры: ' + m.souvenirs.join(' ');
    if (m.user === userKey()) {
      const got = m.got || 0, read = m.read || 0;
      html += '<br><i>📮 письма — в Почтовом Ящике рядом с меткой</i>'
        + '<br>📬 получено ' + got + ' • прочитано ' + read + ' • непрочитано ' + (got - read)
        + '<br><br>☄️ моя ЗвезднаяПыль: <b>' + (m.zp || 0) + '</b>'
        + '<br>💩 мои Какашки: <b>' + (m.poops || 0) + '</b>';
      const myIsl = (lastIslands || []).find(i => (i.owners || [i.owner]).indexOf(userKey()) >= 0);
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
      body: JSON.stringify({chat: chat, user: userKey(), id: id})
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
    const me = (markersData || []).find(m => m.user === userKey());
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
    if (data.from_id && data.from_id !== userKey()) {
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
      body: JSON.stringify({chat: chat, user: userKey(), name: userName(),
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
    if (m.user === userKey()) { status('Выбери метку ДРУГОГО участника, а не свою 🙂'); return; }
    const r = await fetch('/volcano', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: userKey(), to_user: m.user})
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
      mk.bindPopup('💩 Розовая Какашка в пути… (адресат: *****)');
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
    if (m.user === userKey()) { status('Выбери метку ДРУГОГО участника, а не свою 🙂'); return; }
    const r = await fetch('/subgift', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: userKey(), name: userName(), to_user: m.user})
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
      mk.bindPopup('🎁 Подарок в пути… (адресат: *****)');
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
      body: JSON.stringify({chat: chat, user: userKey(), id: id})
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
      body: JSON.stringify({chat: chat, user: userKey()})
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
      body: JSON.stringify({chat: chat, user: userKey(), id: id})
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
    if (isl.guest && isl.guest.user === userKey() && isl.guest.leg === 'staying') {
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
      body: JSON.stringify({chat: chat, user: userKey(), name: userName()})
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
    const others = (lastMarkers || []).filter(xm => xm.user !== userKey());
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
    if (m.user === userKey()) { status('Выбери метку ДРУГОГО участника, а не свою 🙂'); return; }
    const r = await fetch('/islandinvite', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: userKey(), to_user: m.user})
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
      body: JSON.stringify({chat: chat, user: userKey()})
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
      body: JSON.stringify({chat: chat, user: userKey(), building: bid})
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
      body: JSON.stringify({chat: chat, user: userKey()})
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
      body: JSON.stringify({chat: chat, user: userKey()})
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
    if (m.user === userKey()) { status('Выбери метку ДРУГОГО участника, а не свою 🙂'); return; }
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
      body: JSON.stringify({chat: chat, user: userKey(), name: userName(),
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
    const mine = !!markers[userKey()];
    document.getElementById('animals').style.display = mine ? 'none' : 'flex';
    document.getElementById('saveBtn').style.display = mine ? 'none' : '';
    document.getElementById('delBtn').style.display = mine ? '' : 'none';
    nameInput.disabled = mine;
    nameInput.title = mine ? 'Имя закреплено за твоей меткой. Удали метку (🗑 справа), чтобы изменить.' : '';
  }

  async function load() {
    const r = await fetch('/geodata?chat=' + chat + '&user=' + encodeURIComponent(userKey()) + '&t=' + Date.now());
    const data = await r.json();
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
      const haveIsl = lastIslands.some(i => (i.owners || [i.owner]).indexOf(userKey()) >= 0);
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
      + flyingLetters + ' • ☄️ ЗП: ' + (data.stardust || 0)
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
    if (markers[userKey()]) {
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
      body: JSON.stringify({chat: chat, user: userKey(), name: userName(), icon: curIcon,
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
      body: JSON.stringify({chat: chat, user: userKey()})
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

    def _respond(self, code, body=b"", ctype="text/plain; charset=utf-8"):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
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
        elif url.path == "/app":
            self._respond(200, HTML_PAGE.encode("utf-8"), "text/html; charset=utf-8")
        elif url.path == "/canvas":
            chat_id = int(params.get("chat", ["0"])[0])
            state = paint_state.get(chat_id)
            self._respond(200, state["image"] if state else white_png(), "image/png")
        elif url.path == "/geomap":
            self._respond(200, GEO_HTML_PAGE.encode("utf-8"), "text/html; charset=utf-8")
        elif url.path == "/geo2map":
            # бета «ГеографияЧата 2.0» — только для Песочницы
            if int(params.get("chat", ["0"])[0]) != GEO2_CHAT_ID:
                self._respond(403, "beta: only sandbox chat".encode("utf-8"),
                              "text/plain; charset=utf-8")
            else:
                self._respond(200, GEO2_HTML_PAGE.encode("utf-8"), "text/html; charset=utf-8")
        elif url.path == "/geodata":
            chat_id = int(params.get("chat", ["0"])[0])
            viewer = params.get("user", [""])[0]
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
                                f"📬 {dest_name}! Тебе прибыло письмо — открой карту чата "
                                "и нажми на 📬, чтобы прочитать.",
                                ARRIVAL_NOTIFY_TTL_SEC,
                            )
                        except Exception as e:
                            print(f"[paint_bot] уведомление о письме не ушло: {e!r}", flush=True)
                    dest = geo_state.get(chat_id, {}).get(letter["to"])
                    letters_out.append({
                        "id": lid, "lat": round(lat, 6), "lon": round(lon, 6),
                        "arrived": arrived,
                        "read": letter.get("read_ts") is not None,
                        "mine": letter["to"] == viewer,
                        "to": letter["to"],
                        "from_name": letter.get("from_name", "?"),
                        "from": letter["from"],  # user key отправителя — для кнопки «Ответить»
                        "to_name": (dest or {}).get("name", "удалённой метке"),
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
                                f"🌋 Ванильный Вулкан извергся! К тебе, {dest_name}, прилетела "
                                "Розовая Какашка 💩🩷. Примирительно улыбнись и неси в дом — "
                                "принесёт удачу! 😄😊",
                                ARRIVAL_NOTIFY_TTL_SEC,
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
                        "mine": poop["to"] == viewer,
                        "to_name": poop.get("to_name", ""),
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
                        # НЕ автоудаляем — уведомление должно остаться (по требованию владельца)
                        try:
                            tg_send_message(
                                chat_id,
                                f"🎁 {dest_name}! Похотливый Кит прислал тебе подарок — "
                                f"беги открывай! Он уже ждёт у твоей метки 😏🐳",
                            )
                        except Exception as e:
                            print(f"[paint_bot] уведомление о подарке не ушло: {e!r}", flush=True)
                    if gift["arrived"] and gift.get("opened"):
                        continue  # открытый подарок живёт в инфо адресата, маркер снят
                    gifts_out.append({
                        "id": gid, "lat": round(glat, 6), "lon": round(glon, 6),
                        "arrived": garrived,
                        "mine": gift["to"] == viewer,
                        "to": gift["to"],
                        "to_name": gift.get("to_name", ""),
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
                                        f"✈️ {g['name']}! За тобой прилетел самолёт с острова "
                                        f"«{isl['name']}» — тебя зовут в гости! 🏝️😎 "
                                        "Готовь плавки, скоро приземлишься!",
                                        ARRIVAL_NOTIFY_TTL_SEC,
                                    )
                                except Exception as e:
                                    print(f"[paint_bot] уведомление гостю не ушло: {e!r}", flush=True)
                            elif g["leg"] == "to_island":
                                # гость на острове: награды гостю + опыт острову
                                g["leg"] = "staying"
                                isl["visits"] = isl.get("visits", 0) + 1
                                isl["xp"] = isl.get("xp", 0) + 1
                                zp_reward = 2 if "bar" in isl.get("buildings", []) else 1
                                skey = f"{chat_id}|{g['user']}"
                                stardust_state[skey] = stardust_state.get(skey, 0) + zp_reward
                                g["souvenir"] = random.choice(SOUVENIR_PICS)
                                gmarker = geo_state.get(chat_id, {}).get(g["user"])
                                if gmarker is not None:
                                    gmarker.setdefault("souvenirs", []).append(g["souvenir"])
                                try:
                                    tg_send_with_cleanup(
                                        chat_id,
                                        f"🏝️ {g['name']} приземлился на «{isl['name']}»! "
                                        f"+{zp_reward} ЗП и сувенир {g['souvenir']} 😄🎉 "
                                        "Хозяину: гость ждёт — жми «Улететь», когда надоест 🙂",
                                        ARRIVAL_NOTIFY_TTL_SEC,
                                    )
                                except Exception as e:
                                    print(f"[paint_bot] уведомление о госте не ушло: {e!r}", flush=True)
                            else:  # home — гость улетел домой, сессия закрыта
                                gname = g["name"]
                                isl["guest"] = None
                                try:
                                    tg_send_with_cleanup(
                                        chat_id,
                                        f"✈️ {gname} улетел с острова «{isl['name']}» домой. "
                                        "Возвращайся, здесь тепло 🙂",
                                        ARRIVAL_NOTIFY_TTL_SEC,
                                    )
                                except Exception as e:
                                    print(f"[paint_bot] уведомление об отлёте не ушло: {e!r}", flush=True)
                        else:
                            planes_out.append({
                                "island": isl["owner"], "guest_name": g["name"],
                                "leg": g["leg"], "lat": round(plat, 6), "lon": round(plon, 6),
                            })
                    cur_guest = isl.get("guest")
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
                                        "user": cur_guest["user"]}),
                        "mine": viewer in owners,
                    })
                # сувениры гостей — в карточки их меток (видят все) + баланс ЗП каждой метки
                for m in markers:
                    src = geo_state.get(chat_id, {}).get(m["user"])
                    if src and src.get("souvenirs"):
                        m["souvenirs"] = src["souvenirs"]
                    m["zp"] = stardust_get(chat_id, m["user"])
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
                            "meteors": meteors_out, "stardust": stardust_get(chat_id, viewer),
                            "submarine": submarine_out, "gifts": gifts_out,
                            "islands": islands_out, "planes": planes_out},
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
        url = urlparse(self.path)
        if url.path in ("/geomark", "/geodel"):
            self._handle_geo_post(url)
            return
        if url.path in ("/geosend", "/georead"):
            self._handle_letter_post(url)
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
                        "/islandbuild", "/islandpoop", "/islanddel"):
            self._handle_island_post(url)
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
                chat_markers[user] = {
                    "user": user, "name": name, "icon": icon,
                    "lat": round(lat, 6), "lon": round(lon, 6),
                    "got": old.get("got", 0), "read": old.get("read", 0),
                }
            geo_save_to_github()
            self._respond(200, b"ok")
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
                frm, to = markers.get(user), markers.get(to_user)
                if frm is None or to is None:
                    self._json_response(404, {"error": "нет метки у отправителя или адресата"})
                    return
                # гость на острове не принимает почту
                if island_guest_at(chat_id, to_user) is not None:
                    self._json_response(409, {"error": "Адресат в отъезде."})
                    return
                # блокирует отправку только письмо, реально летящее к этому адресату;
                # доставленные/прочитанные не мешают (а удаление писем отключено — иначе
                # первая же доставка вечно блокировала бы пару)
                matched = 0
                for letter in letters_state.values():
                    if letter["chat"] != chat_id or letter["from"] != user or letter["to"] != to_user:
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
                    "id": lid, "chat": chat_id, "from": user, "from_name": name,
                    "to": to_user, "text": text,
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
            if letter["to"] != user:
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
                    dest = geo_state.get(chat_id, {}).get(user)
                    if dest is not None:
                        dest["read"] = dest.get("read", 0) + 1
                result = {
                    "from": letter["from_name"],
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
            key = f"{chat_id}|{user}"
            stardust_state[key] = stardust_state.get(key, 0) + 1
            balance = stardust_state[key]
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
        if stardust_state.get(key, 0) < 1:
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
            stardust_state[key] -= 1
            balance = stardust_state[key]
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
        self._json_response(400, {"error": "kind: volcano|meteor"})

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
            if gift["to"] != user:
                self._json_response(403, {"error": "этот подарок не тебе"})
                return
            _, _, arrived = gift_progress(gift)
            if not arrived:
                self._json_response(409, {"error": "подарок ещё в пути"})
                return
            if gift.get("opened"):
                self._json_response(200, {"picture": gift["picture"],
                                          "from": gift.get("from_name", "?"), "re_open": True})
                return
            gift["opened"] = True
            gift["picture"] = random.choice(GIFT_PICS)
            submarine_save_to_github()
        logline(f"200 /subopen chat={chat_id} user={user!r} gift={gid}")
        self._json_response(200, {"picture": gift["picture"], "from": gift.get("from_name", "?")})
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
        else:
            self._json_response(404, {"error": "not found"})

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
        with geo_lock:
            isl = island_of(chat_id, user)
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
                "Была хорошая легенда 🙂 Владелец может основать новый — за 10 ЗП.",
                300,
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
        with geo_lock:
            if island_of(chat_id, user) is not None:
                self._json_response(409, {"error": "у тебя уже есть остров (можешь быть совладельцем)"})
                return
            if stardust_state.get(key, 0) < ISLAND_COST_ZP:
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
            stardust_state[key] -= ISLAND_COST_ZP
            balance = stardust_state[key]
            islands_save_to_github()
            meteor_save_to_github()
        logline(f"200 /islandbuy chat={chat_id} user={user!r} island={isl_name!r} balance={balance}")
        try:
            tg_send_with_cleanup(
                chat_id,
                f"🏝️ НОВЫЙ ОСТРОВ! На карте чата вырос «{isl_name}». "
                f"Владелец {name} вложил {ISLAND_COST_ZP} ЗП и теперь может звать гостей "
                "самолётом ✈️😎",
                300,  # новость короткоживущая — через 5 минут удаляем, остров остаётся
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
        with geo_lock:
            isl = island_of(chat_id, user)
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
        with geo_lock:
            found = None
            for isl in islands_state.values():
                if isl["chat"] != chat_id:
                    continue
                g = isl.get("guest")
                if g and g["user"] == user and g["leg"] == "staying":
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
        except Exception:
            self._json_response(400, {"error": "bad request"})
            return
        spec = ISLAND_BUILDINGS.get(bid)
        if spec is None:
            self._json_response(400, {"error": "неизвестная постройка"})
            return
        emoji, bname, need_level, cost_zp, cost_poop = spec
        key = f"{chat_id}|{user}"
        with geo_lock:
            isl = island_of(chat_id, user)
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
            if stardust_state.get(key, 0) < cost_zp:
                self._json_response(403, {"error": f"нужно {cost_zp} ЗП (баланс {stardust_state.get(key, 0)})"})
                return
            marker = geo_state.get(chat_id, {}).get(user)
            if cost_poop:
                have = (marker or {}).get("poops", 0)
                if have < cost_poop:
                    self._json_response(403, {"error": f"нужно {cost_poop} розовых какашек (есть {have})"})
                    return
            stardust_state[key] -= cost_zp
            if cost_poop and marker is not None:
                marker["poops"] = marker.get("poops", 0) - cost_poop
            isl.setdefault("buildings", []).append(bid)
            islands_save_to_github()
            meteor_save_to_github()
            geo_save_to_github()
            balance = stardust_state[key]
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
        with geo_lock:
            isl = island_of(chat_id, user)
            if isl is None:
                self._json_response(404, {"error": "сначала купи остров (10 ЗП)"})
                return
            marker = geo_state.get(chat_id, {}).get(user)
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
        [InlineKeyboardButton("🌍 География чата", callback_data="game:geo")],
        [InlineKeyboardButton("🌍✨ ГеографияЧата 2.0 (бета)", callback_data="game:geo2")],
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
    await update.message.reply_text("🎮 Привет! Выбери игру:", reply_markup=GAME_MENU)


async def cmd_myid(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/myid (в личке) — показать свой числовой ID Telegram."""
    if update.message.chat.type != "private":
        return  # только в личке, чтобы не палить ID в группах
    await update.message.reply_text(f"Твой ID Telegram: {update.effective_user.id}")


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
        if not is_private:
            caption += "\n(в группах Telegram кнопка открывает холст в браузере)"
        msg = await context.bot.send_photo(
            chat_id,
            photo=io.BytesIO(state["image"]),
            caption=caption,
            reply_markup=paint_keyboard(chat_id, webapp=is_private, drawer=state["drawer"]),
        )
        state["msg_id"] = msg.message_id
        await query.edit_message_text("🎨 Рисовалка запущена! Лист появился в чате выше — жми «Открыть холст».")
        return

    if game_key == "geo":
        is_private = query.message.chat.type == "private"
        count = len(geo_state.get(chat_id, {}))
        text = (
            "🌍 География чата!\nКаждый участник открывает карту и ставит метку своего города. "
            "Метки общие для этого чата и не видны в других чатах."
            + (f"\nСейчас меток: {count}." if count else "")
        )
        if not is_private:
            text += "\n(в группах кнопка открывает карту в браузере)"
        await context.bot.send_message(chat_id, text, reply_markup=geo_keyboard(chat_id, is_private))
        await query.edit_message_text("🌍 Карта запущена — сообщение с кнопкой появилось в чате выше.")
        return

    if game_key == "geo2":
        if chat_id != GEO2_CHAT_ID:
            await query.answer("🧪 Бета «ГеографияЧата 2.0» пока доступна только в группе Песочница!",
                               show_alert=True)
            return
        text = (
            "🌍✨ ГеографияЧата 2.0 — новая оболочка карты (бета)!\n"
            "Тот же мир: метки, письма, события и острова — но в обновлённом интерфейсе."
        )
        await context.bot.send_message(chat_id, text, reply_markup=geo2_keyboard(chat_id))
        await query.edit_message_text("🌍✨ ГеографияЧата 2.0 — сообщение с кнопкой появилось в чате выше.")
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
                               "started_ts": time.time()}
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


def paint_keyboard(chat_id: int, webapp: bool = True, drawer: str | None = None) -> InlineKeyboardMarkup:
    url = f"{APP_URL}/app?chat={chat_id}"
    if drawer:
        # пока кто-то рисует — кнопка не открывает холст, а сообщает, кто рисует
        btn = InlineKeyboardButton(f"🖌 Рисует {drawer}...", callback_data="paint_wait")
    elif webapp:
        btn = InlineKeyboardButton("🖌 Открыть холст", web_app=WebAppInfo(url=url))
    else:
        btn = InlineKeyboardButton("🖌 Открыть холст (браузер)", url=url)
    return InlineKeyboardMarkup([[btn]])


def geo2_keyboard(chat_id: int) -> InlineKeyboardMarkup:
    """Бета 2.0: кнопка открывает карту (в группах — через браузер)."""
    url = f"{APP_URL}/geo2map?chat={chat_id}"
    return InlineKeyboardMarkup([[InlineKeyboardButton("🌍✨ Открыть карту 2.0", url=url)]])


def geo_keyboard(chat_id: int, webapp: bool) -> InlineKeyboardMarkup:
    url = f"{APP_URL}/geomap?chat={chat_id}"
    if webapp:
        btn = InlineKeyboardButton("🌍 Открыть карту", web_app=WebAppInfo(url=url))
    else:
        btn = InlineKeyboardButton("🌍 Открыть карту (браузер)", url=url)
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
    # Запускаем HTTP-сервер (проверка живости + холст рисовалки) в отдельном потоке
    threading.Thread(target=run_http_server, daemon=True).start()

    app = Application.builder().token(BOT_TOKEN).build()
    app.add_handler(CommandHandler("startsum", cmd_start))
    app.add_handler(CommandHandler("playsum", cmd_play))
    app.add_handler(CommandHandler("secret", cmd_secret))
    app.add_handler(CommandHandler("stop", cmd_stop))
    app.add_handler(CommandHandler("stats", cmd_stats))
    app.add_handler(CommandHandler("helpsum", cmd_help))
    app.add_handler(CommandHandler("myid", cmd_myid))
    app.add_handler(CommandHandler("delpointgeo", cmd_delpointgeo))
    app.add_handler(CallbackQueryHandler(on_game_menu, pattern="^game:"))
    app.add_handler(CallbackQueryHandler(on_saga_action, pattern="^saga:"))
    app.add_handler(CallbackQueryHandler(on_challenge_button, pattern="^duel:"))
    app.add_handler(CallbackQueryHandler(on_paint_wait, pattern="^paint_wait$"))
    app.add_handler(CallbackQueryHandler(on_stop_choice, pattern="^stop:"))
    app.add_handler(CallbackQueryHandler(on_bc_history, pattern="^bc_hist:"))
    app.add_handler(ChatMemberHandler(on_my_chat_member, chat_member_types=ChatMemberHandler.MY_CHAT_MEMBER))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.job_queue.run_repeating(process_paint_updates, interval=1.0)
    app.job_queue.run_repeating(paint_periodic_sweep, interval=15.0)
    # автобэкап меток и писем: каждый день в 01:00 по Москве
    app.job_queue.run_daily(backup_job, time=datetime.time(1, 0, tzinfo=MSK_TZ))
    # вулканы: фоновый спавн + уведомление в чат при появлении
    app.job_queue.run_repeating(volcano_spawn_job, interval=60.0, first=10.0)
    # метеориты: фоновое падение + уведомление в чат
    app.job_queue.run_repeating(meteor_fall_job, interval=60.0, first=20.0)
    # подводные лодки: фоновый спавн в океанах БЕЗ уведомления в чат
    app.job_queue.run_repeating(submarine_spawn_job, interval=60.0, first=30.0)
    app.run_polling()


if __name__ == "__main__":
    main()
