import base64
import io
import json
import os
import queue
import random
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs

from PIL import Image
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, InputMediaPhoto, MessageEntity, Update, WebAppInfo
from telegram.error import BadRequest, Forbidden
from telegram.ext import Application, CallbackQueryHandler, CommandHandler, ContextTypes, MessageHandler, filters

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

# Статистика: {user_id: {"games", "wins", "best"}}
stats = {}

# Известные пользователи (для разрешения @username в id): {username_lower: user_id}
users_by_name = {}


def white_png() -> bytes:
    """Чистый белый лист 900×900 в PNG."""
    img = Image.new("RGB", (900, 900), "white")
    buf = io.BytesIO()
    img.save(buf, "PNG")
    return buf.getvalue()


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
        else:
            self._respond(404, b"not found")

    def do_POST(self):
        url = urlparse(self.path)
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
        state = paint_state.setdefault(
            chat_id, {"image": white_png(), "msg_id": None, "webapp": False}
        )
        state["image"] = png_bytes
        paint_update_queue.put(chat_id)
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
    remember_user(update.effective_user)
    await update.message.reply_text("🎮 Привет! Выбери игру:", reply_markup=GAME_MENU)


async def on_game_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Выбор игры в меню: запускает игру с меткой типа; старую игру игрока завершает."""
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
        state = paint_state.setdefault(
            chat_id, {"image": white_png(), "msg_id": None, "webapp": is_private}
        )
        state["webapp"] = is_private
        caption = "🎨 Общий лист группы! Рисуем по очереди — каждый добавляет штрих."
        if not is_private:
            caption += "\n(в группах Telegram кнопка открывает холст в браузере)"
        msg = await context.bot.send_photo(
            chat_id,
            photo=io.BytesIO(state["image"]),
            caption=caption,
            reply_markup=paint_keyboard(chat_id, webapp=is_private),
        )
        state["msg_id"] = msg.message_id
        await query.edit_message_text("🎨 Рисовалка запущена! Лист появился в чате выше — жми «Открыть холст».")
        return

    await query.answer("Эта игра появится позже 🙂", show_alert=True)


def paint_keyboard(chat_id: int, webapp: bool = True) -> InlineKeyboardMarkup:
    url = f"{APP_URL}/app?chat={chat_id}"
    if webapp:
        btn = InlineKeyboardButton("🖌 Открыть холст", web_app=WebAppInfo(url=url))
    else:
        btn = InlineKeyboardButton("🖌 Открыть холст (браузер)", url=url)
    return InlineKeyboardMarkup([[btn]])


async def process_paint_updates(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Раз в секунду применяет присланные рисунки: редактирует сообщение с листом."""
    while True:
        try:
            chat_id = paint_update_queue.get_nowait()
        except queue.Empty:
            return
        state = paint_state.get(chat_id)
        if state is None:
            continue
        media = InputMediaPhoto(media=io.BytesIO(state["image"]))
        if state["msg_id"] is not None:
            try:
                await context.bot.edit_message_media(
                    chat_id=chat_id, message_id=state["msg_id"], media=media
                )
                continue
            except BadRequest:
                state["msg_id"] = None  # сообщение удалено — пришлём новое ниже
        try:
            msg = await context.bot.send_photo(
                chat_id,
                photo=io.BytesIO(state["image"]),
                caption="🎨 Общий лист группы!",
                reply_markup=paint_keyboard(chat_id, webapp=state.get("webapp", False)),
            )
            state["msg_id"] = msg.message_id
        except Exception:
            pass


async def cmd_stop(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/stop — прервать дуэль (если игрок в ней) или сдаться в соло-игре."""
    remember_user(update.effective_user)
    chat_id = update.message.chat_id
    user = update.effective_user

    duel = duels.get(chat_id)
    if duel is not None and user.id in duel["players"]:
        del duels[chat_id]
        await update.message.reply_text("⚔️ Дуэль прервана по договорённости. Новая — /playsum @игрок")
        return

    if chat_id in paint_state:
        del paint_state[chat_id]
        await update.message.reply_text("🎨 Рисовалка завершена, общий лист стёрт. Новый — через меню /startsum")
        return

    key = (chat_id, user.id)
    game = solo_games.pop(key, None)
    if game is None:
        await update.message.reply_text("У тебя нет активной игры. /startsum — меню игр, /playsum @игрок — дуэль.")
        return
    if game["type"] == "bulls":
        await update.message.reply_text(f"😔 Сдаёшься? Загаданное число было: {game['secret']}.\nНовая игра — /startsum")
    else:
        await update.message.reply_text("Игра завершена.\nНовая игра — /startsum")


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
    remember_user(update.effective_user)
    await update.message.reply_text(HELP_TEXT)


async def cmd_stats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/stats — статистика игрока."""
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


def main() -> None:
    # Запускаем HTTP-сервер (проверка живости + холст рисовалки) в отдельном потоке
    threading.Thread(target=run_http_server, daemon=True).start()

    app = Application.builder().token(BOT_TOKEN).build()
    app.add_handler(CommandHandler("startsum", cmd_start))
    app.add_handler(CommandHandler("playsum", cmd_play))
    app.add_handler(CommandHandler("secret", cmd_secret))
    app.add_handler(CommandHandler("stop", cmd_stop))
    app.add_handler(CommandHandler("stats", cmd_stats))
    app.add_handler(CommandHandler("helpsum", cmd_help))
    app.add_handler(CallbackQueryHandler(on_game_menu, pattern="^game:"))
    app.add_handler(CallbackQueryHandler(on_challenge_button, pattern="^duel:"))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.job_queue.run_repeating(process_paint_updates, interval=1.0)
    app.run_polling()


if __name__ == "__main__":
    main()
