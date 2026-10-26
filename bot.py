import base64
import io
import json
import os
import queue
import random
import threading
import time
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

# География чата: {chat_id: {user_key: {"user", "name", "lat", "lon"}}}
# Хранится в GitHub-репозитории paint-bot-data (файл geo.json), чтобы переживать перезапуски.
geo_state = {}
geo_lock = threading.Lock()

# Репозиторий для данных (не трогать main — иначе каждая метка будет триггерить автодеплой Render)
GEO_REPO = "dbosrsov-cyber/paint-bot-data"
GEO_FILE = "geo.json"
GEO_TOKEN_ENV = "GEO_GITHUB_TOKEN"  # токен добавляется в Render как переменная окружения

# Статистика: {user_id: {"games", "wins", "best"}}
stats = {}

# Известные пользователи (для разрешения @username в id): {username_lower: user_id}
users_by_name = {}

# Доступ: бот работает только в этих группах (личка всегда разрешена)
ALLOWED_GROUPS = {-1004400745434, -1002304715333}
ADMIN_ID = 8668538137  # кому сообщать о добавлении в чужие группы


def chat_allowed(chat) -> bool:
    """Личка — всегда можно; группа/канал — только из белого списка ALLOWED_GROUPS."""
    if chat.type in ("group", "supergroup", "channel"):
        return chat.id in ALLOWED_GROUPS
    return True


# ---------- География чата: сохранение меток в GitHub ----------

def geo_token() -> str:
    return os.environ.get(GEO_TOKEN_ENV, "").strip()


def geo_github_request(method: str, extra_headers: dict | None = None) -> urllib.request.Request:
    headers = {
        "Authorization": f"Bearer {geo_token()}",
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
    }
    headers.update(extra_headers or {})
    return urllib.request.Request(
        f"https://api.github.com/repos/{GEO_REPO}/contents/{GEO_FILE}", headers=headers, method=method
    )


def geo_save_to_github() -> None:
    """Сохранить geo_state в geo.json репозитория данных. Без токена — пропускаем."""
    if not geo_token():
        return
    try:
        with geo_lock:
            payload = json.dumps(geo_state, ensure_ascii=False).encode("utf-8")
        body = {
            "message": "geo: update markers",
            "content": base64.b64encode(payload).decode("ascii"),
        }
        try:
            current = json.load(urllib.request.urlopen(geo_github_request("GET"), timeout=15))
            body["sha"] = current["sha"]
        except urllib.error.HTTPError as e:
            if e.code != 404:
                raise  # файл ещё не создан — пишем без sha
        req = geo_github_request(
            "PUT", {"Content-Type": "application/json"}
        )
        req.data = json.dumps(body).encode("utf-8")
        urllib.request.urlopen(req, timeout=15)
    except Exception as e:
        print(f"[paint_bot] geo save failed: {e!r}", flush=True)


def geo_load_from_github() -> None:
    """Загрузить метки из geo.json при старте сервиса. Без токена или файла — пусто."""
    if not geo_token():
        print("[paint_bot] GEO_GITHUB_TOKEN не задан — метки живут только в памяти", flush=True)
        return
    try:
        data = json.load(urllib.request.urlopen(geo_github_request("GET"), timeout=15))
        raw = base64.b64decode(data["content"]).decode("utf-8")
        loaded = json.loads(raw)
        geo_state.update({int(cid): markers for cid, markers in loaded.items()})
        total = sum(len(m) for m in geo_state.values())
        print(f"[paint_bot] geo: загружено {total} меток из Git", flush=True)
    except urllib.error.HTTPError as e:
        if e.code == 404:
            print("[paint_bot] geo: файла geo.json ещё нет — начинаем с чистого листа", flush=True)
        else:
            print(f"[paint_bot] geo load failed: {e!r}", flush=True)
    except Exception as e:
        print(f"[paint_bot] geo load failed: {e!r}", flush=True)


def white_png() -> bytes:
    """Чистый белый лист 900×900 в PNG."""
    img = Image.new("RGB", (900, 900), "white")
    buf = io.BytesIO()
    img.save(buf, "PNG")
    return buf.getvalue()


# Сколько секунд замок «Рисует...» держится без отправки рисунка
PAINT_LOCK_TIMEOUT = 180


def new_paint_state() -> dict:
    return {
        "image": white_png(),
        "msg_id": None,
        "webapp": False,
        "drawer": None,  # имя того, кто сейчас рисует (мягкая очередь)
        "lock_time": 0.0,
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


# ---------- Страница «География чата» (Leaflet + OpenStreetMap) ----------

GEO_HTML_PAGE = """<!DOCTYPE html>
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
</style>
</head>
<body>
<div id="map"></div>
<div class="bar">
  <input id="name" placeholder="Твоё имя" maxlength="24">
  <button id="saveBtn">📍 Поставить метку</button>
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

  function renderMarker(m) {
    const mk = L.marker([m.lat, m.lon]).addTo(map);
    let html = '<b>' + escapeHtml(m.name) + '</b><br>' + m.lat.toFixed(3) + ', ' + m.lon.toFixed(3);
    if (m.user === userKey()) {
      html += '<br><a href="#" onclick="delMarker(); return false;">🗑 Удалить мою метку</a>';
    }
    mk.bindPopup(html);
    markers[m.user] = mk;
  }

  async function load() {
    const r = await fetch('/geo?chat=' + chat + '&t=' + Date.now());
    const data = await r.json();
    Object.values(markers).forEach(m => map.removeLayer(m));
    Object.keys(markers).forEach(k => delete markers[k]);
    (data.markers || []).forEach(renderMarker);
    status('🌍 Меток в чате: ' + (data.markers || []).length);
  }

  map.on('click', e => {
    pending = e.latlng;
    status('Точка: ' + e.latlng.lat.toFixed(4) + ', ' + e.latlng.lng.toFixed(4) + ' — жми «Поставить метку»');
  });

  document.getElementById('saveBtn').onclick = async () => {
    if (!pending) { status('Сначала кликни по карте в месте своего города'); return; }
    if (nameInput.value.trim()) localStorage.setItem('geo_name', nameInput.value.trim());
    const r = await fetch('/geomark', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: userKey(), name: userName(),
                            lat: pending.lat, lon: pending.lng})
    });
    if (r.ok) { status('✅ Метка поставлена!'); pending = null; load(); }
    else status('Ошибка, попробуй ещё раз');
  };

  async function delMarker() {
    await fetch('/geodel', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({chat: chat, user: userKey()})
    });
    load();
  }
  window.delMarker = delMarker;

  nameInput.onchange = () => { localStorage.setItem('geo_name', nameInput.value.trim()); load(); };
  load();
</script>
</body>
</html>"""


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
        elif url.path == "/app":
            self._respond(200, HTML_PAGE.encode("utf-8"), "text/html; charset=utf-8")
        elif url.path == "/canvas":
            chat_id = int(params.get("chat", ["0"])[0])
            state = paint_state.get(chat_id)
            self._respond(200, state["image"] if state else white_png(), "image/png")
        elif url.path == "/geomap":
            self._respond(200, GEO_HTML_PAGE.encode("utf-8"), "text/html; charset=utf-8")
        elif url.path == "/geo":
            chat_id = int(params.get("chat", ["0"])[0])
            with geo_lock:
                markers = list(geo_state.get(chat_id, {}).values())
            self._respond(
                200,
                json.dumps({"markers": markers}, ensure_ascii=False).encode("utf-8"),
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
                lat = float(payload["lat"])
                lon = float(payload["lon"])
            except Exception:
                self._respond(400, b"bad request")
                return
            if not (-90 <= lat <= 90 and -180 <= lon <= 180):
                self._respond(400, b"bad coords")
                return
            with geo_lock:
                geo_state.setdefault(chat_id, {})[user] = {
                    "user": user, "name": name,
                    "lat": round(lat, 6), "lon": round(lon, 6),
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
            if removed:
                geo_save_to_github()
            self._respond(200, b"ok")

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
        solo_games[key] = {"type": "bulls", "secret": make_secret(), "attempts": 0}
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

    await query.answer("Эта игра появится позже 🙂", show_alert=True)


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

    if not options:
        await update.message.reply_text(
            "Нет активных игр. /startsum — меню игр, /playsum @игрок — дуэль."
        )
        return
    if len(options) == 1:
        await update.message.reply_text(close_activity(chat_id, user.id, options[0][1].split(":", 1)[1]))
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
    text = close_activity(update.effective_chat.id, query.from_user.id, query.data.split(":", 1)[1])
    await query.answer()
    await query.edit_message_text(text)


HELP_TEXT = (
    "📖 Как играть в «Быки и коровы»\n\n"
    "Бот загадывает число из 4 разных цифр (первая — не ноль). Ты называешь "
    "варианты, а бот отвечает:\n"
    "🐂 быки — цифра угадана и стоит на своём месте,\n"
    "🐄 коровы — цифра есть в числе, но стоит не там.\n\n"
    "✍️ Формат хода: сообщение ch1234 — «ch» и сразу 4 цифры, пробелов нет. "
    "На обычные сообщения бот не реагирует.\n\n"
    "▶️ Игры: /startsum — меню выбора (сейчас доступна «Быки и коровы» против компьютера).\n\n"
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
    if bulls == 4:
        st = player_stats(update.effective_user.id)
        st["wins"] += 1
        if st["best"] is None or game["attempts"] < st["best"]:
            st["best"] = game["attempts"]
        del solo_games[key]
        await update.message.reply_text(
            f"🎉 Победа! Число {game['secret']} угадано за {game['attempts']} попыток.\nСыграть ещё — /startsum"
        )
    else:
        await update.message.reply_text(f"{guess} → 🐂 {bulls} · 🐄 {cows} (попытка {game['attempts']})")


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

    if bulls == 4:
        winner_stats = player_stats(user.id)
        winner_stats["wins"] += 1
        if winner_stats["best"] is None or duel["attempts"][user.id] < winner_stats["best"]:
            winner_stats["best"] = duel["attempts"][user.id]
        loser_id = opponent_id
        del duels[chat_id]
        await update.message.reply_text(
            f"🏆 {players[user.id]['name']} угадал число {opponent_secret} за {duel['attempts'][user.id]} попыток!\n"
            f"Победа! {players[user.id]['name']} : {duel['attempts'][user.id]} — {duel['attempts'][loser_id]} : {players[loser_id]['name']}\n"
            f"Реванш — /playsum @игрок"
        )
        return

    duel["turn"] = 1 - duel["turn"]
    next_name = players[duel["order"][duel["turn"]]]["name"]
    await update.message.reply_text(
        f"{players[user.id]['name']}: {guess} → 🐂 {bulls} · 🐄 {cows} (попытка {duel['attempts'][user.id]})\n"
        f"Ход: {next_name}"
    )


async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Точка входа: реагируем только на ходы формата ch1234, всё остальное — молчим."""
    if not chat_allowed(update.effective_chat):
        return
    remember_user(update.effective_user)
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


def main() -> None:
    # Поднимаем сохранённые метки географии из GitHub (после перезапусков)
    geo_load_from_github()
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
    app.add_handler(CallbackQueryHandler(on_challenge_button, pattern="^duel:"))
    app.add_handler(CallbackQueryHandler(on_paint_wait, pattern="^paint_wait$"))
    app.add_handler(CallbackQueryHandler(on_stop_choice, pattern="^stop:"))
    app.add_handler(ChatMemberHandler(on_my_chat_member, chat_member_types=ChatMemberHandler.MY_CHAT_MEMBER))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.job_queue.run_repeating(process_paint_updates, interval=1.0)
    app.run_polling()


if __name__ == "__main__":
    main()
