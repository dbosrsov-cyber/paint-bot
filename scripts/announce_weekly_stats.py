# -*- coding: utf-8 -*-
"""Разовая отправка анонса + пробной сводки «Итоги недели» в «Другое измерение».
Запускается GitHub Actions (scripts/announce_weekly_stats.py), токен — из env BOT_TOKEN."""
import json
import os
import urllib.request

CHAT = -1002304715333

ANNOUNCE = ("🎉 <b>Внимание, жители «Другого измерения»!</b>\n\n"
            "С сегодняшнего дня каждую <b>пятницу в 16:00</b> я буду подводить "
            "итоги недели по 11 номинациям — от глав СагаЧата до морских абордажей 🏆\n"
            "Побеждайте, пишите, топите галеоны — и займите место в списке героев!\n\n"
            "А пока — первая пробная сводка:")

STATS = """🏆 <b>Итоги недели в «Другом измерении»</b>

🐂 <b>Быкующий гений</b> — побед в «Быки и коровы»: ✗
📜 <b>Главный главописец</b> — глав в СагаЧате: ✗
✉️ <b>Почтмейстер</b> — отправлено писем: <b>7</b> — <a href="tg://user?id=769828689">ПМ</a>
📥 <b>Магнит для писем</b> — получено писем: <b>4</b> — <a href="tg://user?id=8668538137">Sumai</a>
💗 <b>Розовощёкий</b> — получено розовых какашек: <b>1</b> — <a href="tg://user?id=8584582199">Андрюха</a>
🎁 <b>Любимчик Дедморозов</b> — получено подарков: <b>13</b> — <a href="tg://user?id=8584582199">Андрюха</a>
✨ <b>Звездочёт</b> — собрано звёздной пыли: <b>8</b> — <a href="tg://user?id=8584582199">Андрюха</a>
⚔️ <b>Морской дьявол</b> — потоплено галеонов (мастер КНБ): ✗
🌊 <b>Корм для акул</b> — поражений при абордаже: <b>4</b> — <a href="tg://user?id=8668538137">Sumai</a>
⚖️ <b>Воротила Рынка</b> — часов владения Морским Рынком: <b>9.4</b> — <a href="tg://user?id=8668538137">Sumai</a>
🐬 <b>Сифа недели</b> — раз получал титул Сифы: ✗"""


def send(text: str) -> int:
    payload = {"chat_id": CHAT, "text": text, "parse_mode": "HTML",
               "disable_web_page_preview": True}
    req = urllib.request.Request(
        f"https://api.telegram.org/bot{os.environ['BOT_TOKEN']}/sendMessage",
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"}, method="POST")
    resp = json.loads(urllib.request.urlopen(req, timeout=30).read())
    if not resp.get("ok"):
        raise RuntimeError(f"Telegram ok=false: {resp}")
    return resp["result"]["message_id"]


if __name__ == "__main__":
    print("announce message_id:", send(ANNOUNCE))
    print("stats message_id:", send(STATS))
