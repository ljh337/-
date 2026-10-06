from __future__ import annotations

import csv
import json
import random
import secrets
import threading
import time
import uuid
from collections import Counter
from pathlib import Path
from typing import Any

from game_common import BASE_DIR, CSV_FIELDS, normalize_csv_header, now_iso


SUITS = ("万", "条", "筒")
TILE_NAMES = tuple(f"{rank + 1}{SUITS[suit]}"
                   for suit in range(3) for rank in range(9))
ALL_TILES = [suit * 9 + rank for suit in range(3)
             for rank in range(9) for _ in range(4)]
PLAYER_COUNT = 4
AI_ACTION_DELAY_SECONDS = 1.6
CSV_PATH = BASE_DIR / "hunan_mahjong_games.csv"
AI_NAMES = ("电脑乙", "电脑丙", "电脑丁")
BIG_PATTERNS = {
    "清一色", "碰碰胡", "将将胡", "七小对", "豪华七小对", "全求人",
    "杠上开花", "抢杠胡", "海底捞月", "河底捞鱼", "天胡", "地胡",
}


def tile_name(tile: int) -> str:
    return TILE_NAMES[tile]


def get_opening_patterns(hand: list[int]) -> set[str]:
    if len(hand) != 14 or any(count > 4 for count in Counter(hand).values()):
        return set()
    patterns = set()
    if not any(tile % 9 + 1 in (2, 5, 8) for tile in hand):
        patterns.add("板板胡")
    if len({tile // 9 for tile in hand}) < 3:
        patterns.add("缺一色")
    counts = Counter(hand)
    if any(count == 4 for count in counts.values()):
        patterns.add("四喜")
    if sum(count >= 3 for count in counts.values()) >= 2:
        patterns.add("六六顺")
    return patterns


def get_win_patterns(hand: list[int], meld_count: int = 0,
                     exposed_melds: list[list[int]] | None = None,
                     meld_open: list[bool] | None = None) -> set[str]:
    exposed_melds = exposed_melds or []
    meld_open = meld_open or []
    if len(hand) != (4 - meld_count) * 3 + 2:
        return set()
    concealed = Counter(hand)
    if any(count > 4 for count in concealed.values()):
        return set()
    full_hand = list(hand) + [tile for meld in exposed_melds for tile in meld]
    patterns: set[str] = set()
    if (meld_count == 0 and len(hand) == 14
            and all(count % 2 == 0 for count in concealed.values())):
        patterns.add("七小对")
        if any(count == 4 for count in concealed.values()):
            patterns.add("豪华七小对")

    def remove_melds(remaining: list[int], needed: int) -> tuple[bool, bool] | None:
        if needed == 0:
            return not any(remaining), not any(remaining)
        first = next((index for index, count in enumerate(remaining) if count), None)
        if first is None:
            return None
        valid = False
        all_triplets = False
        if remaining[first] >= 3:
            remaining[first] -= 3
            result = remove_melds(remaining, needed - 1)
            remaining[first] += 3
            if result and result[0]:
                valid = True
                all_triplets = result[1]
        rank = first % 9
        if rank <= 6 and first // 9 == (first + 1) // 9 == (first + 2) // 9:
            if remaining[first + 1] and remaining[first + 2]:
                remaining[first] -= 1
                remaining[first + 1] -= 1
                remaining[first + 2] -= 1
                result = remove_melds(remaining, needed - 1)
                remaining[first] += 1
                remaining[first + 1] += 1
                remaining[first + 2] += 1
                if result and result[0]:
                    valid = True
        return (valid, all_triplets) if valid else None

    regular_hand = False
    all_triplet_hand = False
    has_258_eye = False
    for eye, count in concealed.items():
        if count < 2:
            continue
        concealed[eye] -= 2
        result = remove_melds(
            [concealed[index] for index in range(27)], 4 - meld_count
        )
        concealed[eye] += 2
        if result and result[0]:
            regular_hand = True
            all_triplet_hand = all_triplet_hand or result[1]
            has_258_eye = has_258_eye or eye % 9 + 1 in (2, 5, 8)
    if not regular_hand:
        return patterns
    if has_258_eye:
        patterns.add("平胡")
    if (all_triplet_hand
            and all(len(set(meld)) == 1 for meld in exposed_melds)):
        patterns.add("碰碰胡")
    if (meld_count == 4 and len(hand) == 2 and len(meld_open) == 4
            and all(meld_open)):
        patterns.add("全求人")
    if len({tile // 9 for tile in full_hand}) == 1:
        patterns.add("清一色")
    if all(tile % 9 + 1 in (2, 5, 8) for tile in full_hand):
        patterns.add("将将胡")
    return patterns


class MahjongService:
    def __init__(self, csv_path: Path = CSV_PATH) -> None:
        self.csv_path = csv_path
        self.games: dict[str, dict[str, Any]] = {}
        self.clients: dict[str, set[tuple[Any, str]]] = {}
        self.ai_running: set[str] = set()
        self.lock = threading.RLock()
        normalize_csv_header(self.csv_path)
        self._load_games()

    def _load_games(self) -> None:
        if not self.csv_path.exists() or not self.csv_path.stat().st_size:
            return
        with self.csv_path.open("r", encoding="utf-16", newline="") as file:
            for row in csv.DictReader(file):
                if row.get("action") == "state_checkpoint":
                    continue
                snapshot = json.loads(row.get("state_json") or "{}")
                if snapshot.get("game_type") == "hunan_mahjong":
                    self.games[snapshot["game_id"]] = snapshot
        for game in self.games.values():
            for player in game["players"]:
                player["connected"] = False

    def _write_event(self, game: dict[str, Any], action: str,
                     player: dict[str, Any] | None = None,
                     details: dict[str, Any] | None = None) -> None:
        game["event_no"] += 1
        event = {
            "event_no": game["event_no"],
            "timestamp": now_iso(),
            "action": action,
            "player_name": player["name"] if player else "系统",
            "seat": player["seat"] if player else None,
            "details": details or {},
        }
        game["events"].append(event)
        fresh = not self.csv_path.exists() or self.csv_path.stat().st_size == 0
        with self.csv_path.open(
            "a", encoding="utf-16" if fresh else "utf-16-le", newline=""
        ) as file:
            writer = csv.DictWriter(file, fieldnames=CSV_FIELDS)
            if fresh:
                writer.writeheader()
            writer.writerow({
                "timestamp": event["timestamp"],
                "game_id": game["game_id"],
                "event_no": event["event_no"],
                "action": action,
                "player_id": player["id"] if player else "",
                "player_name": event["player_name"],
                "details_json": json.dumps(details or {}, ensure_ascii=False),
                "state_json": json.dumps(
                    game, ensure_ascii=False, separators=(",", ":")
                ),
            })

    def create_game(self, title: str, human_count: int) -> dict[str, Any]:
        if isinstance(human_count, bool) or not isinstance(human_count, int) \
                or not 1 <= human_count <= PLAYER_COUNT:
            raise ValueError("麻将真人玩家数量必须为 1 到 4 人")
        with self.lock:
            game_id = f"M{secrets.token_hex(3).upper()}"
            while game_id in self.games:
                game_id = f"M{secrets.token_hex(3).upper()}"
            players = []
            for seat in range(PLAYER_COUNT):
                human = seat < human_count
                players.append({
                    "id": uuid.uuid4().hex[:12],
                    "token": "",
                    "name": f"等待玩家 {seat + 1}" if human else AI_NAMES[seat - human_count],
                    "seat": seat,
                    "human": human,
                    "ready": not human,
                    "connected": not human,
                    "hand": [],
                    "melds": [],
                    "meld_open": [],
                    "discards": [],
                    "score": 0,
                })
            game = {
                "game_type": "hunan_mahjong",
                "game_id": game_id,
                "title": title.strip()[:40] or f"长沙麻将 {len(self.games) + 1}",
                "human_count": human_count,
                "created_at": now_iso(),
                "closed_at": None,
                "phase": "lobby",
                "round_no": 0,
                "players": players,
                "wall": [],
                "dealer": 0,
                "current": 0,
                "needs_draw": False,
                "last_discard": None,
                "last_discarder": None,
                "last_discard_was_last": False,
                "first_discard_pending": True,
                "pending_claim": None,
                "claim_queue": [],
                "pending_added_kong": None,
                "last_draw_was_kong": [False] * PLAYER_COUNT,
                "last_draw_was_last": [False] * PLAYER_COUNT,
                "winner": None,
                "rematch_votes": [],
                "message": f"等待 {human_count} 位真人玩家加入并准备",
                "events": [],
                "event_no": 0,
            }
            self.games[game_id] = game
            self._write_event(game, "game_created", details={
                "game_type": "hunan_mahjong",
                "title": game["title"], "human_count": human_count,
            })
            return self.admin_view(game)

    def join_game(self, game_id: str, name: str) -> dict[str, str]:
        with self.lock:
            game = self.games.get(game_id.upper())
            if not game:
                raise ValueError("没有找到该麻将牌局")
            if game["phase"] != "lobby":
                raise ValueError("本局已经开始，无法加入")
            player = next((p for p in game["players"]
                           if p["human"] and not p["token"]), None)
            if player is None:
                raise ValueError("本桌真人座位已满")
            clean_name = name.strip()
            if not clean_name or len(clean_name) > 8:
                raise ValueError("玩家昵称不能为空且不能超过 8 个字符")
            if any(p["human"] and p["token"] and p["name"] == clean_name
                   for p in game["players"]):
                raise ValueError("该昵称已在本局使用")
            player["name"] = clean_name
            player["token"] = secrets.token_urlsafe(24)
            player["connected"] = True
            game["message"] = f"{clean_name} 加入麻将牌局"
            self._write_event(game, "player_joined", player)
            return {"game_id": game["game_id"], "token": player["token"]}

    def _player_by_token(self, game: dict[str, Any], token: str) -> dict[str, Any]:
        for player in game["players"]:
            if player["human"] and player["token"] \
                    and secrets.compare_digest(player["token"], token):
                return player
        raise ValueError("玩家身份无效，请重新加入麻将牌局")

    def _deal(self, game: dict[str, Any]) -> None:
        wall = ALL_TILES.copy()
        random.SystemRandom().shuffle(wall)
        for player in game["players"]:
            player["hand"] = sorted(
                [wall.pop() for _ in range(14 if player["seat"] == game["dealer"] else 13)]
            )
            player["melds"] = []
            player["meld_open"] = []
            player["discards"] = []
            player["ready"] = not player["human"]
        game["wall"] = wall
        game["phase"] = "playing"
        game["current"] = game["dealer"]
        game["needs_draw"] = False
        game["last_discard"] = None
        game["last_discarder"] = None
        game["last_discard_was_last"] = False
        game["first_discard_pending"] = True
        game["pending_claim"] = None
        game["claim_queue"] = []
        game["pending_added_kong"] = None
        game["last_draw_was_kong"] = [False] * PLAYER_COUNT
        game["last_draw_was_last"] = [False] * PLAYER_COUNT
        game["winner"] = None
        game["round_no"] += 1
        game["rematch_votes"] = []
        game["message"] = "新局开始，庄家先打出一张牌"
        opening = get_opening_patterns(game["players"][game["dealer"]]["hand"])
        regular = get_win_patterns(game["players"][game["dealer"]]["hand"])
        if regular:
            opening.add("天胡")
        if opening:
            self._award_win(game, game["dealer"], game["players"][game["dealer"]]["hand"],
                            True, opening)

    def action(self, game_id: str, token: str, action: str,
               payload: dict[str, Any] | None = None) -> None:
        payload = payload or {}
        with self.lock:
            game = self.games.get(game_id.upper())
            if not game:
                raise ValueError("麻将牌局不存在")
            player = self._player_by_token(game, token)
            seat = player["seat"]
            if action == "ready":
                if game["phase"] != "lobby":
                    raise ValueError("当前阶段不能切换准备状态")
                player["ready"] = not player["ready"]
                self._write_event(game, "ready_changed", player,
                                  {"ready": player["ready"]})
                humans = [p for p in game["players"] if p["human"]]
                if all(p["token"] and p["ready"] for p in humans):
                    self._deal(game)
                    self._write_event(game, "dealt")
                else:
                    game["message"] = (
                        f"{player['name']}{'已准备' if player['ready'] else '取消准备'}"
                    )
                return
            if action == "rematch":
                if game["phase"] != "finished":
                    raise ValueError("本局尚未结束")
                game["rematch_votes"].append(seat)
                humans = [p for p in game["players"] if p["human"]]
                if all(p["seat"] in game["rematch_votes"] for p in humans):
                    self._deal(game)
                    self._write_event(game, "rematch_started", player)
                else:
                    game["message"] = (
                        f"{player['name']} 确认再开一局 "
                        f"({len(game['rematch_votes'])}/{game['human_count']})"
                    )
                    self._write_event(game, "rematch_voted", player, {
                        "votes": len(game["rematch_votes"]),
                        "required": game["human_count"],
                    })
                return
            if game["phase"] != "playing":
                raise ValueError("牌局当前不能操作")
            pending = game["pending_claim"]
            if pending:
                if pending["seat"] != seat:
                    raise ValueError("还没有轮到你响应")
                options = pending["options"]
                if action == "hu" and "hu" in options:
                    self._award_win(
                        game, seat, game["players"][seat]["hand"] + [pending["tile"]],
                        False, pending.get("extra_patterns", []),
                    )
                    return
                if action in ("peng", "gang") and action in options:
                    self._resolve_human_claim(game, player, action)
                    return
                if action == "pass":
                    game["claim_queue"].pop(0)
                    game["pending_claim"] = None
                    self._write_event(game, "passed", player)
                    self._resolve_claim_queue(game)
                    return
                raise ValueError("该响应当前不可用")
            if seat != game["current"]:
                raise ValueError("还没有轮到你")
            if action == "draw":
                if not game["needs_draw"]:
                    raise ValueError("当前不能摸牌")
                self._draw_tile(game, player)
                return
            if action == "discard":
                if game["needs_draw"]:
                    raise ValueError("请先摸牌")
                if len(player["hand"]) % 3 != 2:
                    raise ValueError("当前手牌数量不允许打牌")
                try:
                    hand_index = int(payload.get("tile_index"))
                    tile = sorted(player["hand"])[hand_index]
                except (IndexError, TypeError, ValueError):
                    raise ValueError("请选择有效的手牌")
                player["hand"].remove(tile)
                player["hand"].sort()
                player["discards"].append(tile)
                self._after_discard(game, player, tile)
                return
            if action == "hu":
                patterns = get_win_patterns(
                    player["hand"], len(player["melds"]),
                    player["melds"], player["meld_open"],
                )
                if not patterns:
                    raise ValueError("当前手牌不符合胡牌条件")
                extras = set()
                if game["last_draw_was_kong"][seat]:
                    extras.add("杠上开花")
                if game["last_draw_was_last"][seat]:
                    extras.add("海底捞月")
                self._award_win(game, seat, player["hand"], True, extras)
                return
            if action == "gang":
                self._kong(game, player)
                return
            raise ValueError("不支持的麻将操作")

    def _after_discard(self, game: dict[str, Any], player: dict[str, Any],
                       tile: int) -> None:
        game["last_discard"] = tile
        game["last_discarder"] = player["seat"]
        game["last_discard_was_last"] = game["last_draw_was_last"][player["seat"]]
        game["last_draw_was_last"][player["seat"]] = False
        game["last_draw_was_kong"][player["seat"]] = False
        game["first_discard_pending"] = False
        self._write_event(game, "discarded", player, {"tile": tile_name(tile)})
        queue = []
        for offset in range(1, PLAYER_COUNT):
            seat = (player["seat"] + offset) % PLAYER_COUNT
            other = game["players"][seat]
            patterns = get_win_patterns(
                other["hand"] + [tile], len(other["melds"]),
                other["melds"], other["meld_open"],
            )
            extra = []
            if game["last_discard_was_last"]:
                extra.append("河底捞鱼")
            if patterns:
                queue.append({"seat": seat, "options": ["hu"],
                              "extra_patterns": extra})
        for offset in range(1, PLAYER_COUNT):
            seat = (player["seat"] + offset) % PLAYER_COUNT
            copies = game["players"][seat]["hand"].count(tile)
            options = (["gang", "peng"] if copies >= 3
                       else ["peng"] if copies >= 2 else [])
            if options:
                queue.append({"seat": seat, "options": options,
                              "extra_patterns": []})
        game["claim_queue"] = queue
        game["pending_claim"] = None
        self._resolve_claim_queue(game)

    def _resolve_claim_queue(self, game: dict[str, Any]) -> None:
        while game["claim_queue"] and game["phase"] == "playing":
            claim = game["claim_queue"][0]
            player = game["players"][claim["seat"]]
            if player["human"]:
                game["pending_claim"] = claim
                game["current"] = player["seat"]
                game["message"] = (
                    f"{player['name']} 可对 {tile_name(game['last_discard'])}"
                    f"响应：{'、'.join(claim['options'])}，或选择过"
                )
                return
            game["claim_queue"].pop(0)
            if "hu" in claim["options"]:
                self._award_win(
                    game, player["seat"], player["hand"] + [game["last_discard"],
                    ], False, claim["extra_patterns"],
                )
                return
            action = "gang" if "gang" in claim["options"] else "peng"
            self._apply_claim(game, player, action)
            return
        game["pending_claim"] = None
        if game["phase"] == "playing":
            game["current"] = (game["last_discarder"] + 1) % PLAYER_COUNT
            game["needs_draw"] = True
            game["message"] = f"轮到{game['players'][game['current']]['name']}摸牌"

    def _resolve_human_claim(self, game: dict[str, Any], player: dict[str, Any],
                             action: str) -> None:
        game["claim_queue"].pop(0)
        game["pending_claim"] = None
        self._apply_claim(game, player, action)

    def _apply_claim(self, game: dict[str, Any], player: dict[str, Any],
                     action: str) -> None:
        tile = game["last_discard"]
        remove_count = 3 if action == "gang" else 2
        for _ in range(remove_count):
            player["hand"].remove(tile)
        player["melds"].append([tile] * (remove_count + 1))
        player["meld_open"].append(True)
        game["current"] = player["seat"]
        game["needs_draw"] = action == "gang"
        game["last_discard"] = None
        game["last_discarder"] = None
        game["claim_queue"] = []
        self._write_event(game, action, player, {"tile": tile_name(tile)})
        if action == "gang":
            self._draw_tile(game, player, kong=True)
        else:
            game["message"] = f"{player['name']}碰牌后请打出一张手牌"

    def _kong(self, game: dict[str, Any], player: dict[str, Any]) -> None:
        counts = Counter(player["hand"])
        tile = next((value for value, count in counts.items() if count == 4), None)
        if tile is not None:
            for _ in range(4):
                player["hand"].remove(tile)
            player["melds"].append([tile] * 4)
            player["meld_open"].append(False)
            self._write_event(game, "gang", player, {"tile": tile_name(tile), "concealed": True})
            self._draw_tile(game, player, kong=True)
            return
        meld_index = next((
            index for index, meld in enumerate(player["melds"])
            if len(meld) == 3 and counts[meld[0]]
        ), None)
        if meld_index is None:
            raise ValueError("当前没有可开的杠")
        tile = player["melds"][meld_index][0]
        player["hand"].remove(tile)
        player["melds"][meld_index].append(tile)
        self._write_event(game, "gang", player, {
            "tile": tile_name(tile), "added": True,
        })
        self._draw_tile(game, player, kong=True)

    def _draw_tile(self, game: dict[str, Any], player: dict[str, Any],
                   kong: bool = False) -> None:
        if not game["wall"]:
            self._finish_draw(game)
            return
        tile = game["wall"].pop()
        player["hand"].append(tile)
        player["hand"].sort()
        seat = player["seat"]
        game["current"] = seat
        game["needs_draw"] = False
        game["last_draw_was_kong"][seat] = kong
        game["last_draw_was_last"][seat] = not game["wall"]
        game["message"] = f"{player['name']}摸牌"
        self._write_event(game, "drawn", player, {"tile": tile_name(tile)})

    def _award_win(self, game: dict[str, Any], winner: int, hand: list[int],
                   self_draw: bool, extra_patterns: Any = ()) -> None:
        game["phase"] = "finished"
        game["winner"] = winner
        game["pending_claim"] = None
        game["claim_queue"] = []
        patterns = get_win_patterns(
            hand, len(game["players"][winner]["melds"]),
            game["players"][winner]["melds"],
            game["players"][winner]["meld_open"],
        )
        patterns.update(extra_patterns)
        points = 6 if patterns & BIG_PATTERNS else 1
        if self_draw:
            for seat, player in enumerate(game["players"]):
                player["score"] += points * 3 if seat == winner else -points
        else:
            loser = game["last_discarder"]
            game["players"][winner]["score"] += points
            if loser is not None:
                game["players"][loser]["score"] -= points
        pattern_text = "、".join(sorted(patterns)) or "平胡"
        game["message"] = (
            f"{game['players'][winner]['name']}"
            f"{'自摸' if self_draw else '接炮胡'}：{pattern_text}（{points}分）"
        )
        self._write_event(game, "won", game["players"][winner], {
            "self_draw": self_draw, "patterns": sorted(patterns), "points": points,
        })

    def _finish_draw(self, game: dict[str, Any]) -> None:
        game["phase"] = "finished"
        game["winner"] = None
        game["message"] = "牌墙摸完，本局流局"
        self._write_event(game, "draw_game")

    def schedule_ai(self, game_id: str) -> None:
        with self.lock:
            game = self.games.get(game_id)
            if (not game or game_id in self.ai_running
                    or game["phase"] != "playing"):
                return
            if game["pending_claim"]:
                seat = game["pending_claim"]["seat"]
            else:
                seat = game["current"]
            if game["players"][seat]["human"]:
                return
            self.ai_running.add(game_id)
        threading.Thread(target=self._run_ai, args=(game_id,), daemon=True).start()

    def _run_ai(self, game_id: str) -> None:
        try:
            while True:
                time.sleep(AI_ACTION_DELAY_SECONDS)
                with self.lock:
                    game = self.games.get(game_id)
                    if not game or game["phase"] != "playing":
                        return
                    if game["pending_claim"]:
                        claim = game["pending_claim"]
                        player = game["players"][claim["seat"]]
                        if player["human"]:
                            return
                        game["claim_queue"].pop(0)
                        game["pending_claim"] = None
                        if "hu" in claim["options"]:
                            self._award_win(
                                game, player["seat"],
                                player["hand"] + [game["last_discard"]],
                                False, claim["extra_patterns"],
                            )
                        else:
                            action = (
                                "gang" if "gang" in claim["options"] else "peng"
                            )
                            self._apply_claim(game, player, action)
                    else:
                        player = game["players"][game["current"]]
                        if player["human"]:
                            return
                        if game["needs_draw"]:
                            self._draw_tile(game, player)
                            if game["phase"] != "playing":
                                self.broadcast(game_id)
                                return
                            patterns = get_win_patterns(
                                player["hand"], len(player["melds"]),
                                player["melds"], player["meld_open"],
                            )
                            if patterns:
                                extras = set()
                                if game["last_draw_was_last"][player["seat"]]:
                                    extras.add("海底捞月")
                                self._award_win(
                                    game, player["seat"], player["hand"], True, extras
                                )
                        elif (patterns := get_win_patterns(
                                player["hand"], len(player["melds"]),
                                player["melds"], player["meld_open"])) \
                                and game["last_draw_was_kong"][player["seat"]]:
                            self._award_win(
                                game, player["seat"], player["hand"], True,
                                patterns | {"杠上开花"},
                            )
                        elif self._ai_kong(game, player):
                            pass
                        else:
                            tile = self._ai_discard(player["hand"])
                            player["hand"].remove(tile)
                            player["discards"].append(tile)
                            self._after_discard(game, player, tile)
                    self.broadcast(game_id)
                    if game["phase"] != "playing":
                        return
                    if game["pending_claim"]:
                        if game["players"][game["pending_claim"]["seat"]]["human"]:
                            return
                    elif game["players"][game["current"]]["human"]:
                        return
        except OSError as error:
            print(f"麻将 AI 操作写入 CSV 失败（牌局 {game_id}）: {error}")
        finally:
            with self.lock:
                self.ai_running.discard(game_id)
            self.schedule_ai(game_id)

    def _ai_kong(self, game: dict[str, Any], player: dict[str, Any]) -> bool:
        counts = Counter(player["hand"])
        tile = next((value for value, count in counts.items() if count == 4), None)
        if tile is None:
            return False
        for _ in range(4):
            player["hand"].remove(tile)
        player["melds"].append([tile] * 4)
        player["meld_open"].append(False)
        self._write_event(game, "gang", player, {
            "tile": tile_name(tile), "concealed": True,
        })
        self._draw_tile(game, player, kong=True)
        return True

    @staticmethod
    def _ai_discard(hand: list[int]) -> int:
        counts = Counter(hand)

        def discard_value(tile: int) -> tuple[bool, int, float]:
            neighbors = sum(
                counts.get(tile + offset, 0)
                for offset in (-2, -1, 1, 2)
                if 0 <= tile + offset < 27
                and (tile + offset) // 9 == tile // 9
            )
            return counts[tile] > 1, neighbors, random.random()

        return min(hand, key=discard_value)

    def player_view(self, game: dict[str, Any], token: str) -> dict[str, Any]:
        player = self._player_by_token(game, token)
        message = game["message"]
        last_event = game["events"][-1] if game["events"] else None
        if (last_event and last_event["action"] == "drawn"
                and last_event.get("seat") == player["seat"]):
            message = f"你摸到 {last_event['details']['tile']}"
        return {
            "game_id": game["game_id"],
            "title": game["title"],
            "phase": game["phase"],
            "round_no": game["round_no"],
            "human_count": game["human_count"],
            "seat": player["seat"],
            "players": [{
                "seat": p["seat"], "name": p["name"], "human": p["human"],
                "joined": bool(p["token"]) if p["human"] else True,
                "connected": p["connected"] if p["human"] else True,
                "ready": p["ready"], "card_count": len(p["hand"]),
                "melds": [[tile_name(tile) for tile in meld] for meld in p["melds"]],
                "meld_open": p["meld_open"],
                "discards": [tile_name(tile) for tile in p["discards"]],
                "score": p["score"],
            } for p in game["players"]],
            "hand": [{"tile": tile, "label": tile_name(tile)}
                     for tile in sorted(player["hand"])],
            "wall_count": len(game["wall"]),
            "dealer": game["dealer"],
            "current": game["current"],
            "needs_draw": game["needs_draw"],
            "last_discard": (
                {"tile": game["last_discard"],
                 "label": tile_name(game["last_discard"]),
                 "seat": game["last_discarder"]}
                if game["last_discard"] is not None else None
            ),
            "pending_claim": (
                game["pending_claim"] if game["pending_claim"]
                and game["pending_claim"]["seat"] == player["seat"] else None
            ),
            "can_hu": bool(get_win_patterns(
                player["hand"], len(player["melds"]),
                player["melds"], player["meld_open"],
            )),
            "can_gang": (
                any(count == 4 for count in Counter(player["hand"]).values())
                or any(
                    len(meld) == 3 and player["hand"].count(meld[0])
                    for meld in player["melds"]
                )
            ),
            "winner": game["winner"],
            "rematch_votes": game["rematch_votes"],
            "message": message,
            "events": [{
                "event_no": event["event_no"], "timestamp": event["timestamp"],
                "action": event["action"], "player_name": event["player_name"],
                "details": (
                    {key: value for key, value in event["details"].items()
                     if key != "tile"}
                    if event["action"] == "drawn"
                    and event.get("seat") != player["seat"]
                    else event["details"]
                ),
            } for event in game["events"][-30:]],
        }

    def admin_view(self, game: dict[str, Any]) -> dict[str, Any]:
        return {
            "game_id": game["game_id"], "title": game["title"],
            "phase": game["phase"], "human_count": game["human_count"],
            "created_at": game["created_at"], "closed_at": game["closed_at"],
            "round_no": game["round_no"], "message": game["message"],
            "players": [{
                "seat": p["seat"], "name": p["name"], "human": p["human"],
                "joined": bool(p["token"]) if p["human"] else True,
                "connected": p["connected"] if p["human"] else True,
                "ready": p["ready"], "card_count": len(p["hand"]),
                "hand": [tile_name(tile) for tile in sorted(p["hand"])],
                "melds": [[tile_name(tile) for tile in meld] for meld in p["melds"]],
                "discards": [tile_name(tile) for tile in p["discards"]],
                "score": p["score"],
            } for p in game["players"]],
            "wall_count": len(game["wall"]),
            "wall": [tile_name(tile) for tile in reversed(game["wall"])],
            "current": game["current"],
            "dealer": game["dealer"], "winner": game["winner"],
            "events": [{
                "timestamp": event["timestamp"], "player_name": event["player_name"],
                "action": event["action"], "details": event["details"],
            } for event in game["events"][-80:]],
        }

    def list_games(self) -> list[dict[str, Any]]:
        with self.lock:
            return [self.admin_view(game) for game in
                    sorted(self.games.values(), key=lambda item: item["created_at"],
                           reverse=True)]

    def close_game(self, game_id: str) -> dict[str, Any]:
        with self.lock:
            game = self.games.get(game_id.upper())
            if not game:
                raise ValueError("麻将牌局不存在")
            if game["phase"] == "closed":
                raise ValueError("麻将房间已经关闭")
            game["phase"] = "closed"
            game["closed_at"] = now_iso()
            game["message"] = "管理员已关闭麻将房间"
            self._write_event(game, "game_closed")
            view = self.admin_view(game)
        self.broadcast(game_id.upper())
        return view

    def register_client(self, game_id: str, token: str, handler: Any) -> None:
        with self.lock:
            game = self.games.get(game_id)
            if not game:
                raise ValueError("麻将牌局不存在")
            player = self._player_by_token(game, token)
            self.clients.setdefault(game_id, set()).add((handler, token))
            player["connected"] = True
            self._write_event(game, "player_connected", player)

    def unregister_client(self, game_id: str, token: str, handler: Any) -> None:
        with self.lock:
            clients = self.clients.get(game_id, set())
            clients.discard((handler, token))
            game = self.games.get(game_id)
            if game and not any(value == token for _, value in clients):
                player = next((p for p in game["players"]
                               if p["token"] == token), None)
                if player:
                    player["connected"] = False
                    self._write_event(game, "player_disconnected", player)

    def broadcast(self, game_id: str) -> None:
        with self.lock:
            game = self.games.get(game_id)
            if not game:
                return
            clients = list(self.clients.get(game_id, set()))
            views = [(handler, self.player_view(game, token))
                     for handler, token in clients]
        for handler, view in views:
            try:
                handler.send_json({"type": "state", "state": view})
            except (OSError, ConnectionError):
                continue

    def handle_message(self, handler: Any, message: dict[str, Any],
                       current: tuple[str, str] | None) -> tuple[str, str] | None:
        kind = message.get("type")
        try:
            if kind == "join":
                credentials = self.join_game(
                    str(message.get("game_id", "")),
                    str(message.get("name", "")),
                )
                game_id, token = credentials["game_id"], credentials["token"]
                self.register_client(game_id, token, handler)
                handler.send_json({"type": "joined", **credentials})
                self.broadcast(game_id)
                return game_id, token
            if kind == "resume":
                game_id = str(message.get("game_id", "")).upper()
                token = str(message.get("token", ""))
                self.register_client(game_id, token, handler)
                handler.send_json({"type": "joined", "game_id": game_id,
                                   "token": token})
                self.broadcast(game_id)
                return game_id, token
            if kind == "action":
                if current is None:
                    raise ValueError("请先加入麻将牌局")
                self.action(current[0], current[1],
                            str(message.get("action", "")), message.get("payload"))
                self.broadcast(current[0])
                self.schedule_ai(current[0])
                return current
            raise ValueError("无效的麻将 WebSocket 消息")
        except (ValueError, OSError) as error:
            handler.send_json({"type": "error", "message": str(error)})
            return current
