import math
import os
import threading
from http.server import BaseHTTPRequestHandler, HTTPServer

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.error import BadRequest
from telegram.ext import Application, CallbackQueryHandler, CommandHandler, ContextTypes

# Токен бота берётся из переменной окружения BOT_TOKEN (задаётся в панели Render)
BOT_TOKEN = os.environ["BOT_TOKEN"]

# Размер холста (количество ячеек по горизонтали и вертикали)
COLS = 16
ROWS = 16

WHITE = "white"
COLORS = ["black", "red", "orange", "yellow", "green", "blue", "purple", "brown"]

EMOJI = {
    "white": "◻️",  # мелкий белый квадрат: чистый лист без видимой сетки
    "black": "⬛",
    "red": "🟥",
    "orange": "🟧",
    "yellow": "🟨",
    "green": "🟩",
    "blue": "🟦",
    "purple": "🟪",
    "brown": "🟫",
}

# Инструменты рисования
TOOLS = {
    "pencil": "✏️ Карандаш",
    "line": "📏 Линия",
    "curve": "〰 Кривая",
    "square": "▫ Квадрат",
    "circle": "◯ Круг",
    "triangle": "△ Треугольник",
}

DEFAULT_TOOL = "pencil"
DEFAULT_COLOR = "black"

# Холсты в памяти: {(chat_id, message_id): {"grid", "tools": {user_id: {"tool","color"}},
# "anchors": {user_id: (r,c)}, "history": [снимки сетки], "last_move": имя}}
canvases = {}


class HealthHandler(BaseHTTPRequestHandler):
    """Мини-сервер: отвечает 200 OK, чтобы Render и мониторинг видели бота живым."""

    def do_GET(self):
        self.send_response(200)
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.end_headers()
        self.wfile.write("paint_bot is running".encode("utf-8"))

    def log_message(self, format, *args):
        pass  # не спамить в логи


def run_health_server():
    port = int(os.environ.get("PORT", "10000"))
    server = HTTPServer(("0.0.0.0", port), HealthHandler)
    server.serve_forever()


# ---------- Геометрия (все координаты — в ячейках сетки) ----------

def put(grid, r, c, color):
    """Закрасить ячейку, если она внутри холста."""
    if 0 <= r < ROWS and 0 <= c < COLS:
        grid[r][c] = color


def draw_line(grid, r0, c0, r1, c1, color):
    """Прямая линия (алгоритм Брезенхема)."""
    dr, dc = abs(r1 - r0), abs(c1 - c0)
    sr = 1 if r0 < r1 else -1
    sc = 1 if c0 < c1 else -1
    err = dc - dr
    r, c = r0, c0
    while True:
        put(grid, r, c, color)
        if r == r1 and c == c1:
            break
        e2 = 2 * err
        if e2 > -dr:
            err -= dr
            c += sc
        if e2 < dc:
            err += dc
            r += sr


def draw_square(grid, r0, c0, r1, c1, color):
    """Прямоугольник по двум противоположным углам (контур)."""
    ra, rb = sorted((r0, r1))
    ca, cb = sorted((c0, c1))
    for r in range(ra, rb + 1):
        put(grid, r, ca, color)
        put(grid, r, cb, color)
    for c in range(ca, cb + 1):
        put(grid, ra, c, color)
        put(grid, rb, c, color)


def draw_circle(grid, r0, c0, r1, c1, color):
    """Окружность: центр (r0,c0), радиус = расстоянию до точки (r1,c1)."""
    radius = int(round(math.hypot(r1 - r0, c1 - c0)))
    x, y = radius, 0
    err = 0
    while x >= y:
        for dx, dy in ((x, y), (y, x), (-y, x), (-x, y), (-x, -y), (-y, -x), (y, -x), (x, -y)):
            put(grid, r0 + dy, c0 + dx, color)
        y += 1
        if err <= 0:
            err += 2 * y + 1
        if err > 0:
            x -= 1
            err -= 2 * x + 1


def draw_triangle(grid, r0, c0, r1, c1, color):
    """Треугольник: (r0,c0)-(r1,c1) — основание, вершина над серединой."""
    mr, mc = (r0 + r1) / 2, (c0 + c1) / 2
    height = max(1, int(round(math.hypot(r1 - r0, c1 - c0) / 2)))
    ar, ac = int(round(mr)) - height, int(round(mc))
    draw_line(grid, r0, c0, r1, c1, color)
    draw_line(grid, r1, c1, ar, ac, color)
    draw_line(grid, ar, ac, r0, c0, color)


def draw_curve(grid, r0, c0, r1, c1, color):
    """Кривая (квадратичная кривая Безье): контрольная точка смещена перпендикулярно."""
    mr, mc = (r0 + r1) / 2, (c0 + c1) / 2
    dr, dc = r1 - r0, c1 - c0
    length = math.hypot(dr, dc) or 1.0
    offset = length / 2
    # перпендикуляр к направлению (dr, dc) — вектор (-dc, dr), нормируем
    pr = mr + (-dc / length) * offset
    pc = mc + (dr / length) * offset
    steps = max(8, int(length * 2))
    for i in range(steps + 1):
        t = i / steps
        r = (1 - t) ** 2 * r0 + 2 * (1 - t) * t * pr + t ** 2 * r1
        c = (1 - t) ** 2 * c0 + 2 * (1 - t) * t * pc + t ** 2 * c1
        put(grid, int(round(r)), int(round(c)), color)


SHAPE_DRAWERS = {
    "line": draw_line,
    "curve": draw_curve,
    "square": draw_square,
    "circle": draw_circle,
    "triangle": draw_triangle,
}

# ---------- Интерфейс ----------

def build_markup(grid: list[list[str]]) -> InlineKeyboardMarkup:
    """Клавиатура: сетка ячеек + панель инструментов + палитра."""
    rows = []
    for r in range(ROWS):
        rows.append(
            [InlineKeyboardButton(EMOJI[grid[r][c]], callback_data=f"c:{r}:{c}") for c in range(COLS)]
        )
    # ряд инструментов
    rows.append([InlineKeyboardButton(name, callback_data=f"tool:{key}") for key, name in TOOLS.items()])
    # ластик, отмена и очистка
    rows.append(
        [
            InlineKeyboardButton("⬜ Ластик", callback_data="erase"),
            InlineKeyboardButton("↩️ Отменить", callback_data="undo"),
            InlineKeyboardButton("🗑 Очистить", callback_data="clear"),
        ]
    )
    # палитра цветов
    rows.append([InlineKeyboardButton(EMOJI[color], callback_data=f"col:{color}") for color in COLORS])
    return InlineKeyboardMarkup(rows)


def render_text(grid: list[list[str]]) -> str:
    return "\n".join("".join(EMOJI[cell] for cell in row) for row in grid)


def header_text(tool: str, color: str, anchor_set: bool, last_move: str | None) -> str:
    text = f"Инструмент: {TOOLS[tool]} | Цвет: {EMOJI[color]}"
    if anchor_set:
        text += "\nТочка 1 установлена — нажмите вторую точку."
    if last_move:
        text += f"\nПоследний ход: {last_move}"
    return text


def push_history(canvas: dict) -> None:
    """Сохранить текущее состояние листа для функции «Отменить» (лимит — 30 ходов)."""
    canvas["history"].append([row[:] for row in canvas["grid"]])
    if len(canvas["history"]) > 30:
        canvas["history"].pop(0)


def display_name(user) -> str:
    return f"@{user.username}" if user.username else (user.first_name or "аноним")


def new_canvas() -> dict:
    return {
        "grid": [[WHITE for _ in range(COLS)] for _ in range(ROWS)],
        "tools": {},
        "anchors": {},
        "history": [],
        "last_move": None,
    }


def user_state(canvas: dict, user_id: int) -> dict:
    return canvas["tools"].setdefault(user_id, {"tool": DEFAULT_TOOL, "color": DEFAULT_COLOR})


# ---------- Обработчики ----------

async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Команда /startsum — создаёт новый белый лист в чате (доступен всем)."""
    canvas = new_canvas()
    msg = await update.message.reply_text(
        "🎨 Чистый лист создан! Выберите инструмент и цвет, затем рисуйте.\n"
        + render_text(canvas["grid"]),
        reply_markup=build_markup(canvas["grid"]),
    )
    canvases[(msg.chat_id, msg.message_id)] = canvas


async def on_button(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()

    key = (query.message.chat_id, query.message.message_id)
    canvas = canvases.get(key)
    if canvas is None:
        await query.answer("Этот холст устарел. Создайте новый командой /startsum", show_alert=True)
        return

    user_id = query.from_user.id
    state = user_state(canvas, user_id)
    data = query.data
    anchor = canvas["anchors"].get(user_id)
    redraw = False

    if data.startswith("tool:"):
        state["tool"] = data.split(":", 1)[1]
        canvas["anchors"].pop(user_id, None)  # смена инструмента сбрасывает точку
        redraw = True
    elif data.startswith("col:"):
        state["color"] = data.split(":", 1)[1]
        redraw = True
    elif data == "erase":
        state["tool"] = "pencil"
        state["color"] = WHITE
        redraw = True
    elif data == "clear":
        push_history(canvas)
        for r in range(ROWS):
            for c in range(COLS):
                canvas["grid"][r][c] = WHITE
        canvas["last_move"] = display_name(query.from_user)
        redraw = True
    elif data == "undo":
        if canvas["history"]:
            canvas["grid"] = canvas["history"].pop()
            canvas["anchors"].pop(user_id, None)
        else:
            await query.answer("Отменять больше нечего.", show_alert=True)
            return
        redraw = True
    elif data.startswith("c:"):
        _, r, c = data.split(":")
        r, c = int(r), int(c)
        if state["tool"] in SHAPE_DRAWERS and state["color"] != WHITE:
            # инструмент-фигура: первая точка — якорь, вторая — рисует фигуру
            if anchor is None:
                canvas["anchors"][user_id] = (r, c)
            else:
                push_history(canvas)
                SHAPE_DRAWERS[state["tool"]](canvas["grid"], anchor[0], anchor[1], r, c, state["color"])
                canvas["anchors"].pop(user_id, None)
                canvas["last_move"] = display_name(query.from_user)
        else:
            # карандаш/ластик: закрасить одну ячейку
            if canvas["grid"][r][c] != state["color"]:
                push_history(canvas)
                put(canvas["grid"], r, c, state["color"])
                canvas["last_move"] = display_name(query.from_user)
        redraw = True

    if not redraw:
        return

    text = header_text(
        state["tool"], state["color"], user_id in canvas["anchors"], canvas["last_move"]
    ) + "\n" + render_text(canvas["grid"])
    try:
        await query.edit_message_text(text=text, reply_markup=build_markup(canvas["grid"]))
    except BadRequest:
        pass  # содержимое не изменилось (например, повторный клик по ячейке того же цвета)


def main() -> None:
    # Запускаем мини-сервер для проверки живости в отдельном потоке
    threading.Thread(target=run_health_server, daemon=True).start()

    app = Application.builder().token(BOT_TOKEN).build()
    app.add_handler(CommandHandler("startsum", cmd_start))
    app.add_handler(CallbackQueryHandler(on_button))
    app.run_polling()


if __name__ == "__main__":
    main()
