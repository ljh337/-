from __future__ import annotations

import os
import uuid
from datetime import datetime, timezone
from pathlib import Path


BASE_DIR = Path(__file__).resolve().parent
CSV_FIELDS = (
    "timestamp",
    "game_id",
    "event_no",
    "action",
    "player_id",
    "player_name",
    "details_json",
    "state_json",
)


def now_iso() -> str:
    return datetime.now(timezone.utc).astimezone().isoformat(timespec="seconds")


def normalize_csv_header(csv_path: Path) -> bool:
    """修复被外部工具整体加上双引号的表头行，其余内容原样保留。

    若表头为 "timestamp,game_id,...,state_json"（整行被引号包裹），
    csv.DictReader 会把它当成唯一列名，导致所有记录读不到 game_id。
    返回是否发生了修复。
    """
    if not csv_path.exists() or csv_path.stat().st_size == 0:
        return False
    content = csv_path.read_bytes()
    if content.startswith(b"\xff\xfe"):
        encoding, bom = "utf-16-le", b"\xff\xfe"
        text = content[2:].decode("utf-16-le")
    elif content.startswith(b"\xfe\xff"):
        encoding, bom = "utf-16-be", b"\xfe\xff"
        text = content[2:].decode("utf-16-be")
    elif content.startswith(b"\xef\xbb\xbf"):
        encoding, bom = "utf-8", b"\xef\xbb\xbf"
        text = content[3:].decode("utf-8")
    else:
        encoding, bom = "utf-8", b""
        text = content.decode("utf-8")

    first, separator, rest = text.partition("\n")
    if not separator:
        return False
    has_cr = first.endswith("\r")
    core = first[:-1] if has_cr else first
    if not (core.startswith('"') and core.endswith('"')):
        return False
    core = core[1:-1]
    if core != ",".join(CSV_FIELDS):
        return False

    new_text = core + ("\r" if has_cr else "") + "\n" + rest
    temporary_path = csv_path.with_name(f".{csv_path.name}.{uuid.uuid4().hex}.tmp")
    try:
        temporary_path.write_bytes(bom + new_text.encode(encoding))
        os.replace(temporary_path, csv_path)
    except OSError:
        temporary_path.unlink(missing_ok=True)
        raise
    return True
