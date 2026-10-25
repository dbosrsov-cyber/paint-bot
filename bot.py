import os
import threading
from http.server import BaseHTTPRequestHandler, HTTPServer

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.error import BadRequest
from telegram.ext import Application, CallbackQueryHandler, CommandHandler, ContextTypes

# Токен бота берётся из переменной окружения BOT_TOKEN (задаётся в панели Render)
BOT_TOKEN = os.environ["BOT_TOKEN"]

# Размер холста (количество ячеек по горизонтали и вертикали)
COLS = 8
ROWS = 8

WHITE = "white"
COLORS = ["black", "red", "orange", "yellow", "green", "blue", "purple", "brown"]

EMOJI = {
    "white": "⬜",
    "black": "⬛",
    "red": "🟥",
    "orange": "🟧",
    "yellow": "🟨",
    "green": "🟩",
    "blue": "🟦",
    "purple": "🟪",
    "brown": "🟫",
}

# Холсты в памяти: {(chat_id, message_id): {"grid": [...], "tools": {user_id: цвет}}}
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


def build_markup(grid: list[list[str]]) -> InlineKeyboardMarkup:
    """Клавиатура: сетка ячеек + панель инструментов (как в Paint)."""
    rows = []
    for r in range(ROWS):
        rows.append(
            [InlineKeyboardButton(EMOJI[grid[r][c]], callback_data=f"c:{r}:{c}") for c in range(COLS)]
        )
    # панель инструментов: палитра цветов
    rows.append([InlineKeyboardButton(EMOJI[color], callback_data=f"t:{color}") for color in COLORS])
    # ластик и очистка листа
    rows.append(
        [
            InlineKeyboardButton("⬜ Ластик", callback_data="t:white"),
            InlineKeyboardButton("🗑 Очистить", callback_data="clear"),
        ]
    )
    return InlineKeyboardMarkup(rows)


def render_text(grid: list[list[str]]) -> str:
    return "\n".join("".join(EMOJI[cell] for cell in row) for row in grid)


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Команда /start — создаёт новый белый лист в чате (доступен всем)."""
    grid = [[WHITE for _ in range(COLS)] for _ in range(ROWS)]
    msg = await update.message.reply_text(
        "🎨 Белый лист создан! Выберите цвет на панели и рисуйте — нажимайте на ячейки.\n" + render_text(grid),
        reply_markup=build_markup(grid),
    )
    canvases[(msg.chat_id, msg.message_id)] = {"grid": grid, "tools": {}}


async def on_button(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()

    key = (query.message.chat_id, query.message.message_id)
    canvas = canvases.get(key)
    if canvas is None:
        await query.answer("Этот холст устарел. Создайте новый командой /start", show_alert=True)
        return

    user_id = query.from_user.id
    data = query.data

    if data.startswith("t:"):
        # выбор инструмента (цвета или ластика)
        canvas["tools"][user_id] = data.split(":", 1)[1]
    elif data == "clear":
        # очистка листа
        for r in range(ROWS):
            for c in range(COLS):
                canvas["grid"][r][c] = WHITE
    elif data.startswith("c:"):
        # рисование выбранным цветом в ячейке
        _, r, c = data.split(":")
        color = canvas["tools"].get(user_id, WHITE)
        canvas["grid"][int(r)][int(c)] = color

    tool = canvas["tools"].get(user_id, WHITE)
    text = f"Ваш цвет: {EMOJI[tool]}\n" + render_text(canvas["grid"])
    try:
        await query.edit_message_text(text=text, reply_markup=build_markup(canvas["grid"]))
    except BadRequest:
        pass  # содержимое не изменилось (например, повторный клик по ячейке того же цвета)


def main() -> None:
    # Запускаем мини-сервер для проверки живости в отдельном потоке
    threading.Thread(target=run_health_server, daemon=True).start()

    app = Application.builder().token(BOT_TOKEN).build()
    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CallbackQueryHandler(on_button))
    app.run_polling()


if __name__ == "__main__":
    main()
