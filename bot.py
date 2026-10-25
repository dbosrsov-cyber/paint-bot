import os
import random
import threading
from http.server import BaseHTTPRequestHandler, HTTPServer

from telegram import Update
from telegram.ext import Application, CommandHandler, ContextTypes, MessageHandler, filters

# Токен бота берётся из переменной окружения BOT_TOKEN (задаётся в панели Render)
BOT_TOKEN = os.environ["BOT_TOKEN"]

# Игры в памяти: {(chat_id, user_id): {"secret": str, "attempts": int}}
games = {}

# Статистика по игрокам: {user_id: {"games": int, "wins": int, "best": int|None}}
stats = {}

RULES = (
    "Я загадал число из 4 разных цифр (первая — не ноль).\n"
    "Отправляй варианты сообщениями из 4 цифр, а я отвечу:\n"
    "🐂 быки — цифра угадана и стоит на своём месте,\n"
    "🐄 коровы — цифра есть в числе, но стоит не там.\n"
    "Угадай число! Команда /stop — сдаться."
)


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


def player_stats(user_id: int) -> dict:
    return stats.setdefault(user_id, {"games": 0, "wins": 0, "best": None})


# ---------- Обработчики ----------

async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Команда /startsum — начать новую игру."""
    key = (update.message.chat_id, update.effective_user.id)
    games[key] = {"secret": make_secret(), "attempts": 0}
    player_stats(update.effective_user.id)["games"] += 1
    await update.message.reply_text("🎲 Игра «Быки и коровы» началась!\n\n" + RULES)


async def cmd_stop(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Команда /stop — сдаться и узнать загаданное число."""
    key = (update.message.chat_id, update.effective_user.id)
    game = games.pop(key, None)
    if game is None:
        await update.message.reply_text("У тебя нет активной игры. Начни командой /startsum")
        return
    await update.message.reply_text(
        f"😔 Сдаёшься? Загаданное число было: {game['secret']}.\nНовая игра — /startsum"
    )


async def cmd_stats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Команда /stats — твоя статистика."""
    st = player_stats(update.effective_user.id)
    if st["games"] == 0:
        await update.message.reply_text("Ты ещё не играл. Начни командой /startsum")
        return
    best = f"{st['best']} попыток" if st["best"] is not None else "—"
    await update.message.reply_text(
        f"📊 Твоя статистика:\n"
        f"Игр: {st['games']}\n"
        f"Побед: {st['wins']}\n"
        f"Лучший результат: {best}"
    )


async def on_guess(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Ответ игрока — попытка угадать число."""
    key = (update.message.chat_id, update.effective_user.id)
    game = games.get(key)
    text = update.message.text.strip()

    if game is None:
        await update.message.reply_text("У тебя нет активной игры. Начни командой /startsum")
        return

    if not (len(text) == 4 and text.isdigit()):
        await update.message.reply_text("Нужно отправить 4 цифры, например: 1234")
        return
    if text[0] == "0":
        await update.message.reply_text("Первая цифра не может быть нулём.")
        return
    if len(set(text)) < 4:
        await update.message.reply_text("Цифры не должны повторяться.")
        return

    game["attempts"] += 1
    bulls, cows = bulls_and_cows(game["secret"], text)

    if bulls == 4:
        user_id = update.effective_user.id
        st = player_stats(user_id)
        st["wins"] += 1
        if st["best"] is None or game["attempts"] < st["best"]:
            st["best"] = game["attempts"]
        del games[key]
        await update.message.reply_text(
            f"🎉 Победа! Число {game['secret']} угадано за {game['attempts']} попыток.\n"
            f"Сыграть ещё — /startsum"
        )
    else:
        await update.message.reply_text(f"{text} → 🐂 {bulls} · 🐄 {cows} (попытка {game['attempts']})")


def main() -> None:
    # Запускаем мини-сервер для проверки живости в отдельном потоке
    threading.Thread(target=run_health_server, daemon=True).start()

    app = Application.builder().token(BOT_TOKEN).build()
    app.add_handler(CommandHandler("startsum", cmd_start))
    app.add_handler(CommandHandler("stop", cmd_stop))
    app.add_handler(CommandHandler("stats", cmd_stats))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_guess))
    app.run_polling()


if __name__ == "__main__":
    main()
