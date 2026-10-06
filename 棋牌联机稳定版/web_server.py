from __future__ import annotations

import base64
import csv
import hashlib
import io
import json
import os
import re
import secrets
import socket
import struct
import threading
import time
import uuid
from collections import Counter
from itertools import combinations
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any
from urllib.parse import parse_qs, urlparse

from game_common import BASE_DIR, CSV_FIELDS, normalize_csv_header, now_iso

PLAYER_HTML = BASE_DIR / "player.html"
ADMIN_HTML = BASE_DIR / "admin.html"
CSV_VIEWER_HTML = BASE_DIR / "csv_viewer.html"
PORTAL_HTML = BASE_DIR / "index.html"
ADMIN_PORTAL_HTML = BASE_DIR / "admin_portal.html"
MAHJONG_PLAYER_HTML = BASE_DIR / "mahjong_player.html"
MAHJONG_ADMIN_HTML = BASE_DIR / "mahjong_admin.html"
CSV_PATH = BASE_DIR / "landlord_games.csv"
HOST = os.environ.get("LANDLORD_HOST", "0.0.0.0")
PORT = int(os.environ.get("LANDLORD_PORT", "8876"))
RANK_NAMES = {**{value: str(value) for value in range(3, 11)},
              11: "J", 12: "Q", 13: "K", 14: "A", 15: "2",
              16: "小王", 17: "大王"}
SUITS = ("♠", "♥", "♣", "♦")
SUIT_ORDER = {suit: index for index, suit in enumerate(SUITS)}
WS_GUID = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"
AI_ACTION_DELAY_SECONDS = 1.6
LANDLORD_REVEAL_SECONDS = 3
COMPUTER_LIKE_NAME = re.compile(
    r"(?:电脑|机器人|系统)|(?:^|[^a-z])"
    r"(?:ai|bot|cpu|robot|computer)(?:$|[^a-z])",
    re.IGNORECASE,
)


def make_deck() -> list[dict[str, Any]]:
    cards = [
        {"id": f"{value}-{suit}", "value": value, "rank": RANK_NAMES[value],
         "suit": suit, "label": f"{RANK_NAMES[value]}{suit}"}
        for value in range(3, 16)
        for suit in SUITS
    ]
    cards.extend([
        {"id": "16-joker", "value": 16, "rank": "小王", "suit": "🃏",
         "label": "小王"},
        {"id": "17-joker", "value": 17, "rank": "大王", "suit": "🃏",
         "label": "大王"},
    ])
    return cards


def sort_hand(hand: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return sorted(
        hand,
        key=lambda card: (
            card["value"],
            SUIT_ORDER.get(card["suit"], len(SUIT_ORDER)),
        ),
    )


def detect_combination(values: list[int]) -> tuple[str, int, int] | None:
    if not values:
        return None
    counts = Counter(values)
    total = len(values)
    quads = sorted(value for value, count in counts.items() if count == 4)
    triples = sorted(value for value, count in counts.items() if count == 3)
    pairs = sorted(value for value, count in counts.items() if count == 2)
    singles = sorted(value for value, count in counts.items() if count == 1)

    if total == 2 and counts.get(16) == counts.get(17) == 1:
        return ("rocket", 99, total)
    if total == 4 and len(quads) == 1:
        return ("bomb", quads[0], total)
    if len(quads) == 1 and total == 6 and len(singles) == 2:
        return ("four_two_single", quads[0], total)
    if len(quads) == 1 and total == 8 and len(pairs) == 2:
        return ("four_two_pairs", quads[0], total)
    if len(triples) == 1 and total == 3:
        return ("triple", triples[0], total)
    if len(triples) == 1 and total == 4 and len(singles) == 1:
        return ("triple_one", triples[0], total)
    if len(triples) == 1 and total == 5 and len(pairs) == 1:
        return ("triple_two", triples[0], total)

    if len(triples) >= 2 and triples[-1] <= 14 and all(
        triples[index + 1] == triples[index] + 1
        for index in range(len(triples) - 1)
    ):
        groups = len(triples)
        if total == 3 * groups:
            return ("plane", triples[-1], total)
        if total == 4 * groups and len(singles) == groups:
            return ("plane_single", triples[-1], total)
        if total == 5 * groups and len(pairs) == groups:
            return ("plane_pairs", triples[-1], total)

    if (total >= 5 and len(singles) == total and singles[-1] <= 14
            and all(singles[index + 1] == singles[index] + 1
                    for index in range(total - 1))):
        return ("straight", singles[-1], total)
    if (total >= 6 and total % 2 == 0 and len(pairs) == total // 2
            and pairs[-1] <= 14 and all(
                pairs[index + 1] == pairs[index] + 1
                for index in range(len(pairs) - 1)
            )):
        return ("straight_pairs", pairs[-1], total)
    if total == 2 and len(pairs) == 1:
        return ("pair", pairs[0], total)
    if total == 1:
        return ("single", values[0], total)
    return None


def can_beat(previous: tuple[str, int, int],
             current: tuple[str, int, int]) -> bool:
    previous_type, previous_main, previous_len = previous
    current_type, current_main, current_len = current
    if current_type == "rocket":
        return True
    if previous_type == "rocket":
        return False
    if current_type == "bomb":
        return previous_type != "bomb" or current_main > previous_main
    if previous_type == "bomb" or current_type != previous_type:
        return False
    if current_type in {
        "straight", "straight_pairs", "plane", "plane_single", "plane_pairs",
        "four_two_single", "four_two_pairs",
    } and current_len != previous_len:
        return False
    return current_main > previous_main


def get_possible_plays(hand_values: list[int]) -> list[tuple[str, int, list[int]]]:
    counts = Counter(hand_values)
    plays: list[tuple[str, int, list[int]]] = []
    for value, count in counts.items():
        if count >= 1:
            plays.append(("single", value, [value]))
        if count >= 2:
            plays.append(("pair", value, [value] * 2))
        if count >= 3:
            plays.append(("triple", value, [value] * 3))
            remaining = counts.copy()
            remaining[value] -= 3
            singles = sorted(v for v, n in remaining.items() if n >= 1 and v != value)
            pairs = sorted(v for v, n in remaining.items() if n >= 2 and v != value)
            plays.extend(("triple_one", value, [value] * 3 + [wing])
                         for wing in singles)
            plays.extend(("triple_two", value, [value] * 3 + [wing] * 2)
                         for wing in pairs)

    for start in range(3, 11):
        for end in range(start + 4, 15):
            needed = list(range(start, end + 1))
            if all(counts.get(value, 0) >= 1 for value in needed):
                plays.append(("straight", end, needed))
    for start in range(3, 13):
        for end in range(start + 2, 15):
            needed = list(range(start, end + 1))
            if all(counts.get(value, 0) >= 2 for value in needed):
                plays.append(("straight_pairs", end,
                              [value for value in needed for _ in range(2)]))
    for start in range(3, 14):
        for end in range(start + 1, 15):
            triples = list(range(start, end + 1))
            if not all(counts.get(value, 0) >= 3 for value in triples):
                continue
            base = [value for value in triples for _ in range(3)]
            plays.append(("plane", end, base))
            remaining = counts.copy()
            for value in triples:
                remaining[value] -= 3
            single_wings = sorted(value for value, count in remaining.items()
                                  if count >= 1 and value not in triples)
            pair_wings = sorted(value for value, count in remaining.items()
                                if count >= 2 and value not in triples)
            plays.extend(("plane_single", end, base + list(wings))
                         for wings in combinations(single_wings, len(triples)))
            plays.extend(("plane_pairs", end, base + [
                value for value in wings for _ in range(2)
            ]) for wings in combinations(pair_wings, len(triples)))

    for value, count in counts.items():
        if count < 4:
            continue
        plays.append(("bomb", value, [value] * 4))
        remaining = counts.copy()
        remaining[value] -= 4
        singles = sorted(v for v, n in remaining.items() if n >= 1 and v != value)
        pairs = sorted(v for v, n in remaining.items() if n >= 2 and v != value)
        plays.extend(("four_two_single", value, [value] * 4 + list(wings))
                     for wings in combinations(singles, 2))
        plays.extend(("four_two_pairs", value, [value] * 4 + [
            wing for wing in wings for _ in range(2)
        ]) for wings in combinations(pairs, 2))
    if counts.get(16) and counts.get(17):
        plays.append(("rocket", 99, [16, 17]))
    return plays


def choose_ai_play(hand: list[dict[str, Any]],
                   previous: dict[str, Any] | None) -> list[int] | None:
    plays = get_possible_plays([card["value"] for card in hand])
    if previous is None:
        normal = [play for play in plays if play[0] not in ("bomb", "rocket")]
        candidates = normal or plays
        candidates.sort(key=lambda play: (-len(play[2]), play[1]))
    else:
        prior = (previous["kind"], previous["main"], len(previous["cards"]))
        candidates = [play for play in plays if can_beat(
            prior, (play[0], play[1], len(play[2]))
        )]
        candidates.sort(key=lambda play: (
            play[0] != previous["kind"], play[0] in ("bomb", "rocket"),
            play[1], len(play[2]),
        ))
    if not candidates:
        return None
    selected: list[int] = []
    remaining = hand.copy()
    for value in candidates[0][2]:
        card = next(card for card in remaining if card["value"] == value)
        selected.append(card["id"])
        remaining.remove(card)
    return selected


class GameService:
    def __init__(self, csv_path: Path = CSV_PATH) -> None:
        self.csv_path = csv_path
        self.games: dict[str, dict[str, Any]] = {}
        self.clients: dict[str, set[tuple[Any, str]]] = {}
        self.ai_running: set[str] = set()
        self.lock = threading.RLock()
        self._ensure_excel_compatible_csv()
        self._load_games()

    def _ensure_excel_compatible_csv(self) -> None:
        if not self.csv_path.exists():
            return
        content = self.csv_path.read_bytes()
        if content and not content.startswith(b"\xff\xfe"):
            if content.startswith(b"\xfe\xff"):
                text = content[2:].decode("utf-16-be")
            elif content.startswith(b"\xef\xbb\xbf"):
                text = content[3:].decode("utf-8")
            else:
                text = content.decode("utf-8")
            temporary_path = self.csv_path.with_name(
                f".{self.csv_path.name}.{uuid.uuid4().hex}.tmp"
            )
            try:
                temporary_path.write_bytes(text.encode("utf-16"))
                os.replace(temporary_path, self.csv_path)
            except OSError:
                temporary_path.unlink(missing_ok=True)
                raise
        normalize_csv_header(self.csv_path)

    def _load_games(self) -> None:
        if not self.csv_path.exists() or self.csv_path.stat().st_size == 0:
            return
        latest: dict[str, dict[str, Any]] = {}
        with self.csv_path.open("r", encoding="utf-16", newline="") as file:
            for row in csv.DictReader(file):
                game_id = row.get("game_id")
                snapshot = row.get("state_json")
                if not game_id or not snapshot:
                    continue
                latest[game_id] = json.loads(snapshot)
        for game_id, game in latest.items():
            game.setdefault("bid_candidate", None)
            game.setdefault("bid_count", 0)
            game.setdefault("rematch_votes", [])
            game.setdefault("closed_at", None)
            game.setdefault("landlord_reveal_cards", [])
            game.setdefault("landlord_reveal_until", 0)
            game.setdefault("landlord_reveal_id", None)
            if game["phase"] == "closed" and not game["closed_at"]:
                close_event = next(
                    (event for event in reversed(game["events"])
                     if event["action"] == "game_closed"),
                    None,
                )
                if close_event:
                    game["closed_at"] = close_event["timestamp"]
            game.setdefault("human_count", sum(
                player.get("human", True) for player in game["players"]
            ))
            for player in game["players"]:
                player.setdefault("human", True)
                player["hand"] = sort_hand(player["hand"])
                player["connected"] = not player["human"]
            self.games[game_id] = game

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
        new_file = not self.csv_path.exists() or self.csv_path.stat().st_size == 0
        encoding = "utf-16" if new_file else "utf-16-le"
        with self.csv_path.open("a", encoding=encoding, newline="") as file:
            writer = csv.DictWriter(file, fieldnames=CSV_FIELDS)
            if new_file:
                writer.writeheader()
            writer.writerow({
                "timestamp": event["timestamp"],
                "game_id": game["game_id"],
                "event_no": event["event_no"],
                "action": action,
                "player_id": player["id"] if player else "",
                "player_name": event["player_name"],
                "details_json": json.dumps(details or {}, ensure_ascii=False),
                "state_json": json.dumps(game, ensure_ascii=False, separators=(",", ":")),
            })

    def create_game(self, title: str = "", human_count: int = 3) -> dict[str, Any]:
        if isinstance(human_count, bool) or not isinstance(human_count, int) or not 1 <= human_count <= 3:
            raise ValueError("真人玩家数量必须为 1、2 或 3")
        with self.lock:
            game_id = secrets.token_hex(3).upper()
            while game_id in self.games:
                game_id = secrets.token_hex(3).upper()
            game = {
                "game_id": game_id,
                "title": title[:40].strip() or f"第 {len(self.games) + 1} 桌",
                "human_count": human_count,
                "created_at": now_iso(),
                "closed_at": None,
                "phase": "lobby",
                "players": [
                    {
                        "id": uuid.uuid4().hex[:12],
                        "token": "",
                        "name": f"等待玩家 {seat + 1}",
                        "seat": seat,
                        "human": True,
                        "ready": False,
                        "connected": False,
                        "hand": [],
                    } if seat < human_count else {
                        "id": uuid.uuid4().hex[:12],
                        "token": "",
                        "name": f"电脑 {seat - human_count + 1}",
                        "seat": seat,
                        "human": False,
                        "ready": True,
                        "connected": True,
                        "hand": [],
                    }
                    for seat in range(3)
                ],
                "bottom": [],
                "landlord": None,
                "current_turn": None,
                "bid_turn": None,
                "bid_count": 0,
                "bid_candidate": None,
                "last_play": None,
                "pass_count": 0,
                "winner": None,
                "rematch_votes": [],
                "message": f"等待 {human_count} 位真人玩家加入并准备",
                "events": [],
                "event_no": 0,
                "round_no": 1,
                "deal_no": 0,
            }
            self.games[game_id] = game
            try:
                self._write_event(game, "game_created", details={
                    "title": game["title"], "human_count": human_count,
                })
            except OSError:
                del self.games[game_id]
                raise
            return self.admin_view(game)

    def _player_by_token(self, game: dict[str, Any], token: str) -> dict[str, Any]:
        for player in game["players"]:
            if player["human"] and player["token"] and secrets.compare_digest(player["token"], token):
                return player
        raise ValueError("玩家身份无效，请重新加入牌局")

    def join_game(self, game_id: str, name: str) -> dict[str, Any]:
        with self.lock:
            game = self.games.get(game_id.upper())
            if not game:
                raise ValueError("没有找到该牌局，请检查房间号")
            if game["phase"] != "lobby":
                raise ValueError("本局已经开始，无法加入")
            player = next((p for p in game["players"]
                           if p["human"] and not p["token"]), None)
            if player is None:
                raise ValueError("本局人数已满")
            clean_name = name.strip()
            if not clean_name:
                raise ValueError("请输入玩家昵称")
            if len(clean_name) > 8:
                raise ValueError("玩家昵称不能超过 8 个字符")
            if COMPUTER_LIKE_NAME.search(clean_name):
                raise ValueError("玩家昵称不能使用与电脑玩家或系统相似的名称")
            if any(other["human"] and other["token"]
                   and other["name"] == clean_name for other in game["players"]):
                raise ValueError("该昵称已在本局使用")
            player["token"] = secrets.token_urlsafe(24)
            player["name"] = clean_name
            player["connected"] = True
            game["message"] = f"{clean_name} 加入牌局"
            self._write_event(game, "player_joined", player,
                              {"seat": player["seat"]})
            return {"game_id": game["game_id"], "token": player["token"]}

    def _deal(self, game: dict[str, Any]) -> None:
        deck = make_deck()
        secrets.SystemRandom().shuffle(deck)
        for seat, player in enumerate(game["players"]):
            player["hand"] = sort_hand(deck[seat * 17:(seat + 1) * 17])
            player["ready"] = not player["human"]
        game["bottom"] = deck[51:]
        game["phase"] = "bidding"
        game["landlord"] = None
        game["current_turn"] = None
        game["bid_turn"] = secrets.randbelow(3)
        game["bid_count"] = 0
        game["bid_candidate"] = None
        game["last_play"] = None
        game["pass_count"] = 0
        game["winner"] = None
        game["rematch_votes"] = []
        game["landlord_reveal_cards"] = []
        game["landlord_reveal_until"] = 0
        game["landlord_reveal_id"] = None
        game["deal_no"] += 1
        game["message"] = f"发牌完成，{game['players'][game['bid_turn']]['name']} 先叫地主"

    def _start_play(self, game: dict[str, Any], player: dict[str, Any]) -> None:
        game["landlord"] = player["seat"]
        game["landlord_reveal_cards"] = [
            card["label"] for card in game["bottom"]
        ]
        game["landlord_reveal_until"] = (
            time.time() + LANDLORD_REVEAL_SECONDS
        )
        game["landlord_reveal_id"] = game["event_no"] + 1
        player["hand"] = sort_hand(player["hand"] + game["bottom"])
        game["bottom"] = []
        game["phase"] = "playing"
        game["current_turn"] = player["seat"]
        game["bid_turn"] = None
        game["bid_candidate"] = None
        game["bid_count"] = 0
        game["last_play"] = None
        game["pass_count"] = 0
        game["message"] = f"{player['name']} 成为地主"

    def action(self, game_id: str, token: str,
               action: str, payload: dict[str, Any] | None = None) -> None:
        if payload is not None and not isinstance(payload, dict):
            raise ValueError("操作参数格式无效")
        payload = payload or {}
        with self.lock:
            game = self.games.get(game_id.upper())
            if not game:
                raise ValueError("牌局不存在")
            player = self._player_by_token(game, token)
            if action == "rematch":
                if game["phase"] != "finished":
                    raise ValueError("只有已结束的牌局可以决定是否再开一局")
                rematch_votes = game.setdefault("rematch_votes", [])
                if player["seat"] in rematch_votes:
                    rematch_votes.remove(player["seat"])
                    game["message"] = (
                        f"{player['name']} 取消再开一局，"
                        f"当前 {len(rematch_votes)}/{game['human_count']} 人确认"
                    )
                    self._write_event(game, "rematch_voted", player, {
                        "confirmed": False,
                        "votes": len(rematch_votes),
                        "required": game["human_count"],
                    })
                    return

                rematch_votes.append(player["seat"])
                humans = [p for p in game["players"] if p["human"]]
                if all(human["seat"] in rematch_votes for human in humans):
                    game["round_no"] += 1
                    round_no = game["round_no"]
                    self._deal(game)
                    game["message"] = (
                        f"第 {round_no} 局开始发牌，"
                        f"{game['players'][game['bid_turn']]['name']} 先叫地主"
                    )
                    self._write_event(game, "rematch_started", player, {
                        "round_no": round_no,
                        "deal_no": game["deal_no"],
                        "first_bidder": game["players"][game["bid_turn"]]["name"],
                    })
                    return

                game["message"] = (
                    f"{player['name']} 确认再开一局，"
                    f"当前 {len(rematch_votes)}/{game['human_count']} 人确认"
                )
                self._write_event(game, "rematch_voted", player, {
                    "confirmed": True,
                    "votes": len(rematch_votes),
                    "required": game["human_count"],
                })
                return
            if action == "ready":
                if game["phase"] != "lobby":
                    raise ValueError("当前阶段不能切换准备状态")
                player["ready"] = not player["ready"]
                game["message"] = f"{player['name']} {'已准备' if player['ready'] else '取消准备'}"
                self._write_event(game, "ready_changed", player,
                                  {"ready": player["ready"]})
                humans = [p for p in game["players"] if p["human"]]
                if all(p["token"] and p["ready"] for p in humans):
                    self._deal(game)
                    self._write_event(game, "dealt", details={
                        "deal_no": game["deal_no"],
                        "first_bidder": game["players"][game["bid_turn"]]["name"],
                    })
                    self.schedule_ai(game["game_id"])
                return
            if action in ("bid", "decline", "rob", "not_rob"):
                self._bid(game, player, action in ("bid", "rob"))
                return
            if action == "play":
                self._play(game, player, payload.get("card_ids"))
                return
            if action == "pass":
                self._pass(game, player)
                return
            raise ValueError("不支持的操作")

    def _bid(self, game: dict[str, Any], player: dict[str, Any],
             bids: bool) -> None:
        if game["phase"] != "bidding":
            raise ValueError("当前不是叫地主阶段")
        if player["seat"] != game["bid_turn"]:
            raise ValueError("还没有轮到你叫地主")
        if game["bid_candidate"] is None:
            action_name = "bid" if bids else "decline"
            if bids:
                game["bid_candidate"] = player["seat"]
                game["bid_count"] = 0
                game["bid_turn"] = (player["seat"] + 1) % 3
                game["message"] = (
                    f"{player['name']} 叫地主，轮到 "
                    f"{game['players'][game['bid_turn']]['name']} 抢地主"
                )
                self._write_event(game, action_name, player, {
                    "bid_candidate": player["seat"],
                })
                return
            game["bid_count"] += 1
            if game["bid_count"] >= 3:
                self._deal(game)
                game["message"] = "无人叫地主，已重新发牌"
                self._write_event(game, "redealt", player, {
                    "deal_no": game["deal_no"],
                    "first_bidder": game["players"][game["bid_turn"]]["name"],
                })
                return
            game["bid_turn"] = (player["seat"] + 1) % 3
            game["message"] = (
                f"{player['name']} 不叫，轮到 "
                f"{game['players'][game['bid_turn']]['name']} 叫地主"
            )
            self._write_event(game, action_name, player)
            return

        action_name = "robbed" if bids else "not_robbed"
        if bids:
            game["bid_candidate"] = player["seat"]
            self._start_play(game, player)
            self._write_event(game, action_name, player, {
                "bid_candidate": player["seat"],
                "landlord": player["seat"],
            })
            return

        game["bid_count"] += 1
        candidate_seat = game["bid_candidate"]
        if game["bid_count"] >= 2:
            self._start_play(game, game["players"][candidate_seat])
            self._write_event(game, action_name, player, {
                "bid_candidate": candidate_seat,
                "landlord": candidate_seat,
            })
            return
        game["bid_turn"] = (player["seat"] + 1) % 3
        game["message"] = (
            f"{player['name']} {'抢' if bids else '不抢'}地主，轮到 "
            f"{game['players'][game['bid_turn']]['name']} 抢地主"
        )
        self._write_event(game, action_name, player, {
            "bid_candidate": candidate_seat,
        })

    def _play(self, game: dict[str, Any], player: dict[str, Any],
              card_ids: Any) -> None:
        if game["phase"] != "playing":
            raise ValueError("当前不是出牌阶段")
        if player["seat"] != game["current_turn"]:
            raise ValueError("还没有轮到你出牌")
        if not isinstance(card_ids, list) or not card_ids:
            raise ValueError("请选择要出的牌")
        if any(not isinstance(card_id, str) for card_id in card_ids):
            raise ValueError("所选牌编号无效")
        if len(card_ids) != len(set(card_ids)):
            raise ValueError("不能重复选择同一张牌")
        own_by_id = {card["id"]: card for card in player["hand"]}
        if any(card_id not in own_by_id for card_id in card_ids):
            raise ValueError("所选牌不属于你的手牌")
        cards = [own_by_id[card_id] for card_id in card_ids]
        combination = detect_combination([card["value"] for card in cards])
        if combination is None:
            raise ValueError("所选牌型不合法")
        previous = game["last_play"]
        if previous and previous["seat"] != player["seat"]:
            previous_combo = (previous["kind"], previous["main"],
                              len(previous["cards"]))
            if not can_beat(previous_combo, combination):
                raise ValueError("所选牌无法压过上一手")

        player["hand"] = [card for card in player["hand"] if card["id"] not in card_ids]
        game["last_play"] = {
            "seat": player["seat"],
            "player_name": player["name"],
            "kind": combination[0],
            "main": combination[1],
            "cards": cards,
        }
        game["pass_count"] = 0
        game["current_turn"] = (player["seat"] + 1) % 3
        game["message"] = f"{player['name']} 出了 {format_cards(cards)}"
        if not player["hand"]:
            game["phase"] = "finished"
            game["winner"] = player["seat"]
            game["message"] = f"{player['name']} 获胜"
        self._write_event(game, "cards_played", player, {
            "cards": [card["label"] for card in cards],
            "kind": combination[0],
            "main": combination[1],
        })

    def _pass(self, game: dict[str, Any], player: dict[str, Any]) -> None:
        if game["phase"] != "playing":
            raise ValueError("当前不是出牌阶段")
        if player["seat"] != game["current_turn"]:
            raise ValueError("还没有轮到你")
        if not game["last_play"] or game["last_play"]["seat"] == player["seat"]:
            raise ValueError("当前没有可以跟牌的牌，不能不出")
        game["pass_count"] += 1
        if game["pass_count"] >= 2:
            winning_seat = game["last_play"]["seat"]
            game["current_turn"] = winning_seat
            game["last_play"] = None
            game["pass_count"] = 0
            game["message"] = f"其他玩家都不出，轮到 {game['players'][winning_seat]['name']} 领出"
        else:
            game["current_turn"] = (player["seat"] + 1) % 3
            game["message"] = f"{player['name']} 不出"
        self._write_event(game, "passed", player)

    def _player_connected(self, game_id: str, token: str) -> bool:
        return any(client_token == token for _, client_token
                   in self.clients.get(game_id, set()))

    def schedule_ai(self, game_id: str) -> None:
        with self.lock:
            game = self.games.get(game_id)
            if not game or game_id in self.ai_running:
                return
            if game["phase"] == "bidding":
                seat = game["bid_turn"]
            elif game["phase"] == "playing":
                seat = game["current_turn"]
            else:
                return
            if seat is None or game["players"][seat]["human"]:
                return
            self.ai_running.add(game_id)
        threading.Thread(target=self._run_ai_turns, args=(game_id,),
                         daemon=True).start()

    def _run_ai_turns(self, game_id: str) -> None:
        try:
            while True:
                with self.lock:
                    game = self.games.get(game_id)
                    if not game:
                        return
                    if game["phase"] == "bidding":
                        seat = game["bid_turn"]
                    elif game["phase"] == "playing":
                        seat = game["current_turn"]
                    else:
                        return
                    if seat is None:
                        return
                    player = game["players"][seat]
                    if player["human"]:
                        return
                    reveal_remaining = max(
                        0,
                        game.get("landlord_reveal_until", 0) - time.time(),
                    )
                time.sleep(max(AI_ACTION_DELAY_SECONDS, reveal_remaining))
                with self.lock:
                    game = self.games.get(game_id)
                    if not game:
                        return
                    if game["phase"] == "bidding":
                        seat = game["bid_turn"]
                    elif game["phase"] == "playing":
                        seat = game["current_turn"]
                    else:
                        return
                    if seat is None:
                        return
                    player = game["players"][seat]
                    if player["human"]:
                        return
                    if game["phase"] == "bidding":
                        strength = sum(max(0, card["value"] - 10)
                                       for card in player["hand"])
                        threshold = 22 if game["bid_candidate"] is not None else 18
                        self._bid(game, player, strength >= threshold)
                    else:
                        previous = game["last_play"]
                        if previous and previous["seat"] == player["seat"]:
                            previous = None
                        card_ids = choose_ai_play(player["hand"], previous)
                        if card_ids is None:
                            self._pass(game, player)
                        else:
                            self._play(game, player, card_ids)
                self.broadcast(game_id)
        except OSError as error:
            print(f"AI 操作写入 CSV 失败（牌局 {game_id}）: {error}")
        finally:
            with self.lock:
                self.ai_running.discard(game_id)
            self.schedule_ai(game_id)

    def player_view(self, game: dict[str, Any], token: str) -> dict[str, Any]:
        player = self._player_by_token(game, token)
        reveal_remaining_ms = max(
            0,
            round((game.get("landlord_reveal_until", 0) - time.time()) * 1000),
        )
        return {
            "game_id": game["game_id"],
            "title": game["title"],
            "human_count": game["human_count"],
            "phase": game["phase"],
            "players": [
                {"name": other["name"], "seat": other["seat"],
                 "ready": other["ready"],
                 "human": other["human"],
                 "joined": bool(other["token"]) if other["human"] else True,
                 "connected": (other["connected"] or self._player_connected(
                     game["game_id"], other["token"])) if other["human"] else True,
                 "card_count": len(other["hand"])}
                for other in game["players"]
            ],
            "seat": player["seat"],
            "hand": player["hand"],
            "bottom": game["bottom"] if game["phase"] == "bidding" else [],
            "landlord_reveal": (
                {
                    "id": game.get("landlord_reveal_id"),
                    "cards": game.get("landlord_reveal_cards", []),
                    "remaining_ms": reveal_remaining_ms,
                }
                if reveal_remaining_ms > 0
                else None
            ),
            "landlord": game["landlord"],
            "current_turn": game["current_turn"],
            "bid_turn": game["bid_turn"],
            "bid_count": game["bid_count"],
            "bid_candidate": game["bid_candidate"],
            "last_play": game["last_play"],
            "pass_count": game["pass_count"],
            "winner": game["winner"],
            "round_no": game["round_no"],
            "rematch_votes": game.get("rematch_votes", []),
            "message": game["message"],
            "events": game["events"][-30:],
        }

    def admin_view(self, game: dict[str, Any]) -> dict[str, Any]:
        current_seat = (
            game["bid_turn"] if game["phase"] == "bidding"
            else game["current_turn"] if game["phase"] == "playing"
            else None
        )
        last_play = game["last_play"]
        return {
            "game_id": game["game_id"],
            "title": game["title"],
            "human_count": game["human_count"],
            "created_at": game["created_at"],
            "closed_at": game.get("closed_at"),
            "phase": game["phase"],
            "message": game["message"],
            "players": [
                {"name": p["name"], "seat": p["seat"], "ready": p["ready"],
                 "human": p["human"],
                 "joined": bool(p["token"]) if p["human"] else True,
                 "connected": (p["connected"] or self._player_connected(
                     game["game_id"], p["token"])) if p["human"] else True,
                 "card_count": len(p["hand"]),
                 "hand": [card["label"] for card in p["hand"]]}
                for p in game["players"]
            ],
            "landlord": game["landlord"],
            "current_turn": game["current_turn"],
            "current_player": (
                game["players"][current_seat]["name"]
                if current_seat is not None else None
            ),
            "bid_turn": game["bid_turn"],
            "bid_candidate": game["bid_candidate"],
            "last_play": ({
                "player_name": last_play["player_name"],
                "cards": [card["label"] for card in last_play["cards"]],
            } if last_play else None),
            "winner": game["winner"],
            "round_no": game["round_no"],
            "rematch_votes": game.get("rematch_votes", []),
            "winner_name": (
                game["players"][game["winner"]]["name"]
                if game["winner"] is not None else None
            ),
            "events": [self._admin_event_view(event)
                       for event in game["events"][-100:]],
        }

    @staticmethod
    def _admin_event_view(event: dict[str, Any]) -> dict[str, Any]:
        details = event["details"]
        action_names = {
            "game_created": "创建房间",
            "player_joined": "玩家加入",
            "player_connected": "玩家上线",
            "player_disconnected": "玩家断开连接",
            "ready_changed": "准备状态变更",
            "dealt": "发牌",
            "bid": "叫地主",
            "robbed": "抢地主",
            "decline": "不叫地主",
            "not_robbed": "不抢地主",
            "redealt": "无人叫地主，重新发牌",
            "cards_played": "出牌",
            "passed": "不出",
            "action_rejected": "操作未执行",
            "game_closed": "管理员关闭房间",
            "rematch_voted": "玩家决定再开一局",
            "rematch_started": "真人玩家全部同意，再开一局",
            "rematch_voted": "玩家决定再开一局",
            "rematch_started": "真人玩家全部同意，再开一局",
        }
        description = action_names.get(event["action"], "牌局操作")
        if event["action"] == "game_created":
            human_count = details.get("human_count")
            if human_count is not None:
                description += f"（{human_count} 位真人，其余为 AI）"
        elif event["action"] == "player_joined":
            description += f"并坐到{event['seat'] + 1}号位"
        elif event["action"] == "ready_changed":
            description = "已准备" if details.get("ready") else "取消准备"
        elif event["action"] == "dealt":
            description += f"（第 {details.get('deal_no', '?')} 轮）"
        elif event["action"] in ("bid", "robbed", "decline", "not_robbed"):
            seat = details.get("bid_candidate")
            if seat is not None:
                description += f"，当前叫地主者：{seat + 1}号位"
        elif event["action"] == "cards_played":
            description += f"：{' '.join(details.get('cards', []))}"
        elif event["action"] == "action_rejected":
            description += f"：{details.get('reason', '操作无效')}"
        return {
            "timestamp": event["timestamp"],
            "player_name": event["player_name"],
            "description": description,
        }

    def list_games(self) -> list[dict[str, Any]]:
        with self.lock:
            return [self.admin_view(game) for game in
                    sorted(self.games.values(), key=lambda item: item["created_at"],
                           reverse=True)]

    def delete_csv_event(self, game_id: str, event_no: int) -> dict[str, Any]:
        normalized_game_id = game_id.strip().upper()
        if not normalized_game_id or event_no < 1:
            raise ValueError("牌局编号或记录序号无效")

        with self.lock:
            if not self.csv_path.exists() or self.csv_path.stat().st_size == 0:
                raise ValueError("CSV 中没有这条记录")
            with self.csv_path.open("r", encoding="utf-16", newline="") as file:
                reader = csv.DictReader(file)
                fieldnames = reader.fieldnames
                rows = list(reader)
            if not fieldnames:
                raise ValueError("CSV 文件缺少表头")

            targets = [
                index for index, row in enumerate(rows)
                if row.get("game_id", "").upper() == normalized_game_id
                and row.get("event_no", "") == str(event_no)
                and row.get("action") != "state_checkpoint"
            ]
            if not targets:
                raise ValueError("CSV 中没有这条记录")
            if len(targets) != 1:
                raise ValueError("记录编号不唯一，无法安全删除")

            target_index = targets[0]
            target = rows[target_index]
            latest_game_index = max(
                index for index, row in enumerate(rows)
                if row.get("game_id", "").upper() == normalized_game_id
            )
            checkpointed = target_index == latest_game_index
            rewritten_rows: list[dict[str, str]] = []
            for index, row in enumerate(rows):
                if row.get("game_id", "").upper() != normalized_game_id:
                    rewritten_rows.append(row)
                    continue

                try:
                    snapshot = json.loads(row.get("state_json") or "{}")
                except json.JSONDecodeError:
                    snapshot = {}
                if isinstance(snapshot, dict) and isinstance(snapshot.get("events"), list):
                    snapshot["events"] = [
                        event for event in snapshot["events"]
                        if not isinstance(event, dict)
                        or event.get("event_no") != event_no
                    ]
                    row["state_json"] = json.dumps(
                        snapshot, ensure_ascii=False, separators=(",", ":")
                    )

                if index == target_index:
                    if not checkpointed:
                        continue
                    row = row.copy()
                    row["action"] = "state_checkpoint"
                    row["player_id"] = ""
                    row["player_name"] = "系统"
                    row["details_json"] = json.dumps({
                        "reason": "deleted_event",
                        "deleted_event_no": event_no,
                        "deleted_action": target.get("action", ""),
                    }, ensure_ascii=False)
                rewritten_rows.append(row)

            temporary_path = self.csv_path.with_name(
                f".{self.csv_path.name}.{uuid.uuid4().hex}.tmp"
            )
            try:
                with temporary_path.open(
                    "w", encoding="utf-16", newline=""
                ) as file:
                    writer = csv.DictWriter(file, fieldnames=fieldnames)
                    writer.writeheader()
                    writer.writerows(rewritten_rows)
                os.replace(temporary_path, self.csv_path)
            except (OSError, csv.Error):
                temporary_path.unlink(missing_ok=True)
                raise

            game = self.games.get(normalized_game_id)
            if game:
                game["events"] = [
                    event for event in game["events"]
                    if event.get("event_no") != event_no
                ]
        return {"deleted": True, "checkpointed": checkpointed}

    def delete_csv_room(self, game_id: str) -> dict[str, Any]:
        result = self.delete_csv_rooms([game_id])
        return {
            "deleted": True,
            "game_id": result["game_ids"][0],
            "deleted_rows": result["deleted_rows"],
        }

    def delete_csv_rooms(self, game_ids: list[str]) -> dict[str, Any]:
        if not game_ids or any(not isinstance(game_id, str) for game_id in game_ids):
            raise ValueError("请选择至少一个有效房间")
        normalized_game_ids = list(dict.fromkeys(
            game_id.strip().upper() for game_id in game_ids
        ))
        if any(not game_id for game_id in normalized_game_ids):
            raise ValueError("房间编号无效")

        with self.lock:
            for normalized_game_id in normalized_game_ids:
                game = self.games.get(normalized_game_id)
                if not game:
                    raise ValueError(f"没有找到房间 {normalized_game_id}")
                if game.get("phase") != "closed":
                    raise ValueError(
                        f"只能删除已关闭房间的数据：{normalized_game_id} 尚未关闭"
                    )
            if not self.csv_path.exists() or self.csv_path.stat().st_size == 0:
                raise ValueError("CSV 中没有所选房间的数据")

            with self.csv_path.open("r", encoding="utf-16", newline="") as file:
                reader = csv.DictReader(file)
                fieldnames = reader.fieldnames
                rows = list(reader)
            if not fieldnames:
                raise ValueError("CSV 文件缺少表头")

            deleted_rows_by_game = {
                game_id: sum(
                    row.get("game_id", "").upper() == game_id for row in rows
                )
                for game_id in normalized_game_ids
            }
            missing_data = [
                game_id for game_id, row_count in deleted_rows_by_game.items()
                if row_count == 0
            ]
            if missing_data:
                raise ValueError(
                    f"CSV 中没有房间 {', '.join(missing_data)} 的数据"
                )
            remaining_rows = [
                row for row in rows
                if row.get("game_id", "").upper() not in normalized_game_ids
            ]

            temporary_path = self.csv_path.with_name(
                f".{self.csv_path.name}.{uuid.uuid4().hex}.tmp"
            )
            try:
                with temporary_path.open("w", encoding="utf-16", newline="") as file:
                    writer = csv.DictWriter(file, fieldnames=fieldnames)
                    writer.writeheader()
                    writer.writerows(remaining_rows)
                os.replace(temporary_path, self.csv_path)
            except (OSError, csv.Error):
                temporary_path.unlink(missing_ok=True)
                raise

            for normalized_game_id in normalized_game_ids:
                del self.games[normalized_game_id]
                self.clients.pop(normalized_game_id, None)

        return {
            "deleted": True,
            "game_ids": normalized_game_ids,
            "deleted_rows": sum(deleted_rows_by_game.values()),
            "deleted_rows_by_game": deleted_rows_by_game,
        }

    def csv_view(self, page: int = 1, page_size: int = 50,
                 game_id: str = "", query: str = "",
                 game_type: str = "") -> dict[str, Any]:
        if page < 1:
            raise ValueError("页码必须大于 0")
        if not 1 <= page_size <= 100:
            raise ValueError("每页条数必须在 1 到 100 之间")
        if game_type not in ("", "landlord", "mahjong"):
            raise ValueError("游戏类型无效")

        sources = []
        if game_type in ("", "landlord"):
            sources.append((self, "landlord"))
        if game_type in ("", "mahjong"):
            sources.append((MAHJONG_SERVICE, "mahjong"))
        rows: list[tuple[dict[str, str], str]] = []
        for service, source_type in sources:
            with service.lock:
                normalize_csv_header(service.csv_path)
                if not service.csv_path.exists() or not service.csv_path.stat().st_size:
                    continue
                with service.csv_path.open("r", encoding="utf-16", newline="") as file:
                    rows.extend((row, source_type) for row in csv.DictReader(file))

        entries: list[dict[str, Any]] = []
        rooms: dict[str, dict[str, Any]] = {}
        normalized_game_id = game_id.strip().upper()
        normalized_query = query.strip().casefold()
        mahjong_tile_names = tuple(
            f"{rank + 1}{suit}" for suit in ("万", "条", "筒")
            for rank in range(9)
        )
        for row, source_type in rows:
            row_game_id = row.get("game_id", "")
            if not row_game_id:
                continue
            try:
                details = json.loads(row.get("details_json") or "{}")
                snapshot = json.loads(row.get("state_json") or "{}")
            except json.JSONDecodeError:
                details = {}
                snapshot = {}
                snapshot_error = "记录中的 JSON 数据无法解析"
            else:
                snapshot_error = ""
            if not isinstance(details, dict):
                details = {}
                snapshot_error = "操作详情不是有效对象"
            if not isinstance(snapshot, dict):
                snapshot = {}
                snapshot_error = "牌局快照不是有效对象"

            title = str(snapshot.get("title") or details.get("title") or row_game_id)
            room = rooms.setdefault(row_game_id, {
                "game_id": row_game_id,
                "title": title,
                "phase": snapshot.get("phase", "unknown"),
                "event_count": 0,
                "game_type": source_type,
            })
            room["title"] = title
            room["phase"] = snapshot.get("phase", "unknown")
            if row.get("action") == "state_checkpoint":
                continue
            room["event_count"] += 1
            players = snapshot.get("players", [])
            snapshot_players = []
            if isinstance(players, list):
                for player in players:
                    if not isinstance(player, dict):
                        continue
                    hand = player.get("hand", [])
                    if not isinstance(hand, list):
                        hand = []
                    if source_type == "mahjong":
                        hand_labels = [
                            mahjong_tile_names[tile]
                            for tile in hand
                            if isinstance(tile, int)
                            and 0 <= tile < len(mahjong_tile_names)
                        ]
                    else:
                        hand_labels = [
                            card.get("label", "?")
                            for card in hand
                            if isinstance(card, dict)
                        ]
                    snapshot_players.append({
                        "seat": player.get("seat"),
                        "name": player.get("name", "未知玩家"),
                        "human": player.get("human", True),
                        "card_count": len(hand),
                        "hand": hand_labels,
                        "melds": player.get("melds", []),
                        "discards": player.get("discards", []),
                    })
            phase = snapshot.get("phase")
            action_names = {
                "game_created": "创建房间",
                "player_joined": "玩家加入",
                "player_connected": "玩家上线",
                "player_disconnected": "玩家断开连接",
                "ready_changed": "准备状态变更",
                "dealt": "发牌",
                "bid": "叫地主",
                "robbed": "抢地主",
                "decline": "不叫地主",
                "not_robbed": "不抢地主",
                "redealt": "无人叫地主，重新发牌",
                "cards_played": "出牌",
                "passed": "不出",
                "action_rejected": "操作未执行",
                "game_closed": "管理员关闭房间",
                "rematch_voted": "玩家决定再开一局",
                "rematch_started": "真人玩家全部同意，再开一局",
                "drawn": "摸牌",
                "discarded": "出牌",
                "peng": "碰牌",
                "gang": "杠牌",
                "won": "胡牌",
                "draw_game": "流局",
                "passed": "过牌",
            }
            action = row.get("action", "")
            action_label = action_names.get(action, "牌局操作")
            if action == "game_created":
                human_count = details.get("human_count")
                if human_count is not None:
                    action_label += f"（{human_count} 位真人，其余为 AI）"
            elif action == "player_joined" and isinstance(details.get("seat"), int):
                action_label += f"并坐到{details['seat'] + 1}号位"
            elif action == "ready_changed":
                action_label = "已准备" if details.get("ready") else "取消准备"
            elif action == "dealt":
                action_label += f"（第 {details.get('deal_no', '?')} 轮）"
            elif action in ("cards_played",):
                cards = details.get("cards", [])
                if isinstance(cards, list):
                    action_label += f"：{' '.join(str(card) for card in cards)}"
            elif action == "action_rejected":
                action_label += f"：{details.get('reason', '操作无效')}"
            elif action == "rematch_voted":
                votes = details.get("votes", "?")
                required = details.get("required", "?")
                action_label = (
                    f"{'确认' if details.get('confirmed') else '取消'}再开一局"
                    f"（{votes}/{required}）"
                )
            event = {
                "timestamp": row.get("timestamp", ""),
                "game_id": row_game_id,
                "game_type": source_type,
                "event_no": row.get("event_no", ""),
                "action": action,
                "action_label": action_label,
                "player_name": row.get("player_name", "系统"),
                "details": details,
                "description": action_label,
                "snapshot": {
                    "title": title,
                    "game_type": source_type,
                    "phase": phase,
                    "message": snapshot.get("message", ""),
                    "landlord": snapshot.get("landlord"),
                    "current_turn": snapshot.get("current_turn"),
                    "current": snapshot.get("current"),
                    "dealer": snapshot.get("dealer"),
                    "wall_count": len(snapshot.get("wall", []))
                    if isinstance(snapshot.get("wall"), list) else 0,
                    "winner": snapshot.get("winner"),
                    "human_count": snapshot.get("human_count", 3 if source_type == "landlord" else 4),
                    "rematch_votes": snapshot.get("rematch_votes", []),
                    "players": snapshot_players,
                } if snapshot else None,
                "snapshot_error": snapshot_error,
            }
            if normalized_game_id and row_game_id.upper() != normalized_game_id:
                continue
            searchable = " ".join((
                event["timestamp"], event["game_id"], event["event_no"],
                event["action"], event["action_label"], event["player_name"], title,
                json.dumps(details, ensure_ascii=False),
                str(event["snapshot"]),
            )).casefold()
            if normalized_query and normalized_query not in searchable:
                continue
            entries.append(event)

        entries.reverse()
        entries.sort(key=lambda event: event["timestamp"], reverse=True)
        total = len(entries)
        start = (page - 1) * page_size
        return {
            "events": entries[start:start + page_size],
            "page": page,
            "page_size": page_size,
            "total": total,
            "rooms": [
                room for room in sorted(
                    rooms.values(), key=lambda item: item["game_id"]
                )
            ],
        }

    def export_csv_game(self, game_id: str) -> tuple[str, bytes]:
        normalized_game_id = game_id.strip().upper()
        if not normalized_game_id:
            raise ValueError("牌局编号无效")

        with self.lock:
            if not self.csv_path.exists() or self.csv_path.stat().st_size == 0:
                raise ValueError("CSV 中没有该牌局的数据")
            with self.csv_path.open("r", encoding="utf-16", newline="") as file:
                rows = list(csv.DictReader(file))

        room_rows = [
            row for row in rows
            if row.get("game_id", "").upper() == normalized_game_id
            and row.get("action") != "state_checkpoint"
        ]
        if not room_rows:
            raise ValueError("CSV 中没有该牌局的数据")

        headers = [
            "时间", "房间名称", "房间号", "操作序号", "第几局", "操作类型",
            "操作玩家", "操作说明", "操作补充信息", "游戏阶段",
            "当前牌局提示", "地主", "当前操作玩家", "胜者",
        ]
        for seat in range(3):
            headers.extend([
                f"座位{seat + 1}玩家", f"座位{seat + 1}类型",
                f"座位{seat + 1}剩余牌数", f"座位{seat + 1}当时手牌",
            ])

        action_names = {
            "game_created": "创建房间",
            "player_joined": "玩家加入",
            "player_connected": "玩家上线",
            "player_disconnected": "玩家断开连接",
            "ready_changed": "准备状态变更",
            "dealt": "发牌",
            "bid": "叫地主",
            "robbed": "抢地主",
            "decline": "不叫地主",
            "not_robbed": "不抢地主",
            "redealt": "无人叫地主，重新发牌",
            "cards_played": "出牌",
            "passed": "不出",
            "action_rejected": "操作未执行",
            "game_closed": "管理员关闭房间",
            "rematch_voted": "玩家决定再开一局",
            "rematch_started": "真人玩家全部同意，再开一局",
        }
        phases = {
            "lobby": "等待玩家", "bidding": "叫地主", "playing": "进行中",
            "finished": "已结束", "closed": "已关闭",
        }
        output = io.StringIO(newline="")
        writer = csv.writer(output)
        writer.writerow(headers)

        for row in room_rows:
            try:
                details = json.loads(row.get("details_json") or "{}")
                snapshot = json.loads(row.get("state_json") or "{}")
            except json.JSONDecodeError as error:
                raise ValueError(
                    f"第 {row.get('event_no', '?')} 条记录的状态数据无法解析"
                ) from error
            if not isinstance(details, dict) or not isinstance(snapshot, dict):
                raise ValueError(
                    f"第 {row.get('event_no', '?')} 条记录的数据格式无效"
                )

            action = row.get("action", "")
            description = action_names.get(action, "牌局操作")
            if action == "game_created":
                human_count = details.get("human_count")
                if human_count is not None:
                    description += f"（{human_count} 位真人，其余为 AI）"
            elif action == "player_joined" and isinstance(details.get("seat"), int):
                description += f"并坐到{details['seat'] + 1}号位"
            elif action == "ready_changed":
                description = "已准备" if details.get("ready") else "取消准备"
            elif action == "dealt":
                description += f"（第 {details.get('deal_no', '?')} 轮）"
            elif action == "cards_played":
                cards = details.get("cards", [])
                if isinstance(cards, list):
                    description += f"：{' '.join(str(card) for card in cards)}"
            elif action == "action_rejected":
                description += f"：{details.get('reason', '操作无效')}"
            elif action == "rematch_voted":
                description = (
                    f"{'确认' if details.get('confirmed') else '取消'}再开一局"
                    f"（{details.get('votes', '?')}/{details.get('required', '?')}）"
                )
            detail_labels = {
                "seat": "座位", "ready": "准备状态", "deal_no": "发牌轮次",
                "first_bidder": "首位叫地主", "bid_candidate": "当前叫地主者",
                "landlord": "地主座位", "cards": "牌面", "reason": "原因",
                "action": "操作", "confirmed": "确认再开",
                "votes": "已确认人数", "required": "所需人数",
                "human_count": "真人玩家数", "title": "房间名称",
            }
            readable_details = []
            for key, value in details.items():
                label = detail_labels.get(key, key)
                if key in ("seat", "bid_candidate", "landlord") and isinstance(value, int):
                    value = f"{value + 1}号位"
                elif key in ("ready", "confirmed") and isinstance(value, bool):
                    value = "是" if value else "否"
                elif isinstance(value, list):
                    value = " ".join(str(item) for item in value)
                elif isinstance(value, dict):
                    value = json.dumps(value, ensure_ascii=False)
                readable_details.append(f"{label}：{value}")
            detail_text = "；".join(readable_details)

            players = snapshot.get("players", [])
            if not isinstance(players, list):
                players = []
            players_by_seat = {
                player.get("seat"): player for player in players
                if isinstance(player, dict) and isinstance(player.get("seat"), int)
            }
            landlord_seat = snapshot.get("landlord")
            current_seat = snapshot.get("current_turn")
            if current_seat is None:
                current_seat = snapshot.get("bid_turn")
            winner_seat = snapshot.get("winner")
            exported_row: list[str | int] = [
                row.get("timestamp", ""),
                snapshot.get("title") or normalized_game_id,
                normalized_game_id,
                row.get("event_no", ""),
                snapshot.get("round_no", 1),
                action_names.get(action, "牌局操作"),
                row.get("player_name", "系统"),
                description,
                detail_text,
                phases.get(snapshot.get("phase"), snapshot.get("phase", "未知")),
                snapshot.get("message", ""),
                (
                    players_by_seat.get(landlord_seat, {}).get("name", "")
                    if isinstance(landlord_seat, int) else ""
                ),
                (
                    players_by_seat.get(current_seat, {}).get("name", "")
                    if isinstance(current_seat, int) else ""
                ),
                (
                    players_by_seat.get(winner_seat, {}).get("name", "")
                    if isinstance(winner_seat, int) else ""
                ),
            ]
            for seat in range(3):
                player = players_by_seat.get(seat, {})
                hand = player.get("hand", [])
                if not isinstance(hand, list):
                    hand = []
                labels = [
                    str(card.get("label", "?"))
                    for card in hand if isinstance(card, dict)
                ]
                exported_row.extend([
                    player.get("name", ""),
                    "真人" if player.get("human", True) else "AI",
                    len(labels),
                    " ".join(labels) if labels else "无",
                ])

            writer.writerow([
                "'" + str(value)
                if isinstance(value, str)
                and value.lstrip().startswith(("=", "+", "-", "@"))
                else value
                for value in exported_row
            ])

        filename = f"landlord-game-{normalized_game_id}.csv"
        return filename, ("\ufeff" + output.getvalue()).encode("utf-8")

    def admin_game(self, game_id: str) -> dict[str, Any]:
        with self.lock:
            game = self.games.get(game_id.upper())
            if not game:
                raise ValueError("牌局不存在")
            return self.admin_view(game)

    def close_game(self, game_id: str) -> dict[str, Any]:
        with self.lock:
            game = self.games.get(game_id.upper())
            if not game:
                raise ValueError("牌局不存在")
            if game["phase"] == "closed":
                raise ValueError("房间已经关闭")
            game["phase"] = "closed"
            game["closed_at"] = now_iso()
            game["message"] = "管理员已关闭房间"
            self._write_event(game, "game_closed")
            view = self.admin_view(game)
        self.broadcast(game_id.upper())
        return view

    def register_client(self, game_id: str, token: str,
                        handler: Any) -> None:
        with self.lock:
            game = self.games.get(game_id.upper())
            if not game:
                raise ValueError("牌局不存在")
            self._player_by_token(game, token)
            self.clients.setdefault(game["game_id"], set()).add((handler, token))
            player = self._player_by_token(game, token)
            player["connected"] = True
            self._write_event(game, "player_connected", player)

    def unregister_client(self, game_id: str, token: str,
                          handler: Any) -> None:
        with self.lock:
            clients = self.clients.get(game_id, set())
            clients.discard((handler, token))
            game = self.games.get(game_id)
            if game:
                player = next((p for p in game["players"] if p["token"] == token), None)
                if player and not self._player_connected(game_id, token):
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
                game_id = credentials["game_id"]
                token = credentials["token"]
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
                    raise ValueError("请先加入牌局")
                self.action(current[0], current[1],
                            str(message.get("action", "")), message.get("payload"))
                self.broadcast(current[0])
                self.schedule_ai(current[0])
                return current
            raise ValueError("无效的消息类型")
        except (ValueError, OSError) as error:
            if kind == "action" and current:
                with self.lock:
                    game = self.games.get(current[0])
                    if game:
                        player = self._player_by_token(game, current[1])
                        self._write_event(game, "action_rejected", player, {
                            "action": message.get("action"),
                            "payload": message.get("payload", {}),
                            "reason": str(error),
                        })
                        self.broadcast(current[0])
            handler.send_json({"type": "error", "message": str(error)})
            return current


def format_cards(cards: list[dict[str, Any]]) -> str:
    return " ".join(card["label"] for card in
                    sorted(cards, key=lambda card: card["value"], reverse=True))


SERVICE = GameService()
from mahjong_service import MahjongService

MAHJONG_SERVICE = MahjongService()
ADMIN_PASSWORD = secrets.token_urlsafe(24)
ADMIN_SESSION_TOKEN = ""
ADMIN_SESSION_LOCK = threading.Lock()


def create_admin_session(password: str) -> str:
    global ADMIN_SESSION_TOKEN
    if not secrets.compare_digest(password, ADMIN_PASSWORD):
        raise PermissionError("管理口令错误")
    with ADMIN_SESSION_LOCK:
        if ADMIN_SESSION_TOKEN:
            raise PermissionError("管理端已有设备在线，请先在该设备点击“下线”")
        ADMIN_SESSION_TOKEN = secrets.token_urlsafe(32)
        return ADMIN_SESSION_TOKEN


def clear_admin_session(token: str) -> None:
    global ADMIN_SESSION_TOKEN
    with ADMIN_SESSION_LOCK:
        if token and ADMIN_SESSION_TOKEN and secrets.compare_digest(
            token, ADMIN_SESSION_TOKEN
        ):
            ADMIN_SESSION_TOKEN = ""


def websocket_frame(payload: bytes, opcode: int = 1) -> bytes:
    length = len(payload)
    header = bytearray([0x80 | opcode])
    if length < 126:
        header.append(length)
    elif length < 65536:
        header.append(126)
        header.extend(struct.pack("!H", length))
    else:
        header.append(127)
        header.extend(struct.pack("!Q", length))
    return bytes(header) + payload


class RequestHandler(BaseHTTPRequestHandler):
    server_version = "LandlordTunnel/1.0"

    def log_message(self, fmt: str, *args: Any) -> None:
        print(f"[{now_iso()}] {self.address_string()} {fmt % args}")

    def _headers(self, status: int, content_type: str,
                 length: int | None = None) -> None:
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "same-origin")
        self.send_header("Content-Security-Policy",
                         "default-src 'self'; connect-src 'self' ws: wss:; "
                         "style-src 'self' 'unsafe-inline'; "
                         "script-src 'self' 'unsafe-inline'; "
                         "img-src 'self' data:; base-uri 'none'; frame-ancestors 'none'")
        if length is not None:
            self.send_header("Content-Length", str(length))
        self.end_headers()

    def _send_json(self, data: Any, status: int = 200) -> None:
        body = json.dumps(data, ensure_ascii=False).encode("utf-8")
        self._headers(status, "application/json; charset=utf-8", len(body))
        self.wfile.write(body)

    def _read_json(self) -> dict[str, Any]:
        try:
            length = int(self.headers.get("Content-Length", "0"))
        except ValueError as error:
            raise ValueError("请求长度无效") from error
        if length <= 0 or length > 65536:
            raise ValueError("请求内容为空或过大")
        try:
            data = json.loads(self.rfile.read(length))
        except (json.JSONDecodeError, UnicodeDecodeError) as error:
            raise ValueError("JSON 格式无效") from error
        if not isinstance(data, dict):
            raise ValueError("请求内容必须是对象")
        return data

    def _require_admin(self) -> None:
        token = self.headers.get("X-Admin-Token", "")
        with ADMIN_SESSION_LOCK:
            if not token or not ADMIN_SESSION_TOKEN or not secrets.compare_digest(
                token, ADMIN_SESSION_TOKEN
            ):
                raise PermissionError("管理会话已失效，请重新登录")

    def do_GET(self) -> None:
        if urlparse(self.path).path in ("/ws", "/ws/mahjong"):
            self._websocket()
            return
        parsed = urlparse(self.path)
        path = parsed.path
        if path == "/":
            game_type = parse_qs(parsed.query).get("game", [""])[0]
            self._serve_file(
                MAHJONG_PLAYER_HTML if game_type == "mahjong"
                else PLAYER_HTML if game_type == "landlord"
                else PORTAL_HTML
            )
        elif path == "/admin":
            self._serve_file(ADMIN_HTML)
        elif path == "/landlord":
            self._serve_file(PLAYER_HTML)
        elif path in ("/landlord-admin", "/mahjong-admin"):
            self._serve_file(ADMIN_HTML)
        elif path == "/mahjong":
            self._serve_file(MAHJONG_PLAYER_HTML)
        elif path == "/csv-viewer":
            self._serve_file(CSV_VIEWER_HTML)
        elif path == "/health":
            self._send_json({"ok": True})
        elif path.startswith("/api/rooms/"):
            room_id = path[len("/api/rooms/"):].upper()
            if not room_id or "/" in room_id:
                self._send_json({"error": "房间号格式无效"}, 400)
                return
            with SERVICE.lock:
                landlord_game = SERVICE.games.get(room_id)
            with MAHJONG_SERVICE.lock:
                mahjong_game = MAHJONG_SERVICE.games.get(room_id)
            game = landlord_game or mahjong_game
            if not game:
                self._send_json({"error": "没有找到该房间，请确认房间号后重试"}, 404)
            elif game["phase"] == "closed":
                self._send_json({"error": "该房间已关闭"}, 410)
            else:
                self._send_json({
                    "game_type": "mahjong" if mahjong_game else "landlord"
                })
        elif path == "/api/admin/games":
            try:
                self._require_admin()
                self._send_json({"games": SERVICE.list_games()})
            except PermissionError as error:
                self._send_json({"error": str(error)}, 403)
        elif path == "/api/mahjong/admin/games":
            try:
                self._require_admin()
                self._send_json({"games": MAHJONG_SERVICE.list_games()})
            except PermissionError as error:
                self._send_json({"error": str(error)}, 403)
        elif path.startswith("/api/mahjong/admin/games/"):
            try:
                self._require_admin()
                game_id = path.rsplit("/", 1)[-1]
                game = MAHJONG_SERVICE.games.get(game_id.upper())
                if not game:
                    raise ValueError("麻将牌局不存在")
                self._send_json({"game": MAHJONG_SERVICE.admin_view(game)})
            except PermissionError as error:
                self._send_json({"error": str(error)}, 403)
            except ValueError as error:
                self._send_json({"error": str(error)}, 404)
        elif path == "/api/admin/csv":
            try:
                self._require_admin()
                params = parse_qs(parsed.query)
                page = int(params.get("page", ["1"])[0])
                page_size = int(params.get("page_size", ["50"])[0])
                result = SERVICE.csv_view(
                    page=page,
                    page_size=page_size,
                    game_id=params.get("game_id", [""])[0],
                    query=params.get("q", [""])[0],
                    game_type=params.get("game_type", [""])[0],
                )
                self._send_json(result)
            except PermissionError as error:
                self._send_json({"error": str(error)}, 403)
            except ValueError as error:
                self._send_json({"error": f"CSV 查看参数无效：{error}"}, 400)
            except OSError as error:
                print(f"CSV 查看失败: {error}")
                self._send_json({"error": "无法读取牌局 CSV，请检查文件状态"}, 500)
            except csv.Error as error:
                print(f"CSV 格式错误: {error}")
                self._send_json({"error": "CSV 文件格式错误，无法读取"}, 500)
        elif path.startswith("/api/admin/csv/") and path.endswith("/export"):
            try:
                self._require_admin()
                game_id = path[len("/api/admin/csv/"):-len("/export")].strip("/")
                filename, body = SERVICE.export_csv_game(game_id)
                self.send_response(200)
                self.send_header("Content-Type", "text/csv; charset=utf-8")
                self.send_header(
                    "Content-Disposition", f'attachment; filename="{filename}"'
                )
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Cache-Control", "no-store")
                self.send_header("X-Content-Type-Options", "nosniff")
                self.end_headers()
                self.wfile.write(body)
            except PermissionError as error:
                self._send_json({"error": str(error)}, 403)
            except ValueError as error:
                self._send_json({"error": str(error)}, 404)
            except OSError as error:
                print(f"单局 CSV 导出失败: {error}")
                self._send_json({"error": "无法读取牌局 CSV，请检查文件状态"}, 500)
            except csv.Error as error:
                print(f"CSV 格式错误: {error}")
                self._send_json({"error": "CSV 文件格式错误，无法导出"}, 500)
        elif path.startswith("/api/admin/games/"):
            try:
                self._require_admin()
                game_id = path.rsplit("/", 1)[-1]
                self._send_json({"game": SERVICE.admin_game(game_id)})
            except PermissionError as error:
                self._send_json({"error": str(error)}, 403)
            except ValueError as error:
                self._send_json({"error": str(error)}, 404)
        else:
            self._send_json({"error": "没有找到页面"}, 404)

    def do_POST(self) -> None:
        path = urlparse(self.path).path
        if path == "/api/admin/session":
            try:
                data = self._read_json()
                session_token = create_admin_session(str(data.get("password", "")))
                self._send_json({"token": session_token})
            except PermissionError as error:
                self._send_json({"error": str(error)}, 403)
            except ValueError as error:
                self._send_json({"error": str(error)}, 400)
            except OSError as error:
                print(f"CSV 房间数据批量删除失败: {error}")
                self._send_json({"error": "无法安全更新 CSV，请检查文件状态和目录权限"}, 500)
            except csv.Error as error:
                print(f"CSV 格式错误: {error}")
                self._send_json({"error": "CSV 文件格式错误，无法安全删除房间数据"}, 500)
            return
        if path == "/api/mahjong/admin/games":
            try:
                self._require_admin()
                data = self._read_json()
                human_count = data.get("human_count", 4)
                if isinstance(human_count, str) and human_count.isdecimal():
                    human_count = int(human_count)
                game = MAHJONG_SERVICE.create_game(
                    str(data.get("title", "")), human_count
                )
                forwarded_proto = self.headers.get(
                    "X-Forwarded-Proto", "http"
                ).split(",")[0]
                host = self.headers.get("Host", f"localhost:{PORT}")
                game["invite_url"] = (
                    f"{forwarded_proto}://{host}/?game=mahjong"
                    f"&room={game['game_id']}"
                )
                self._send_json({"game": game}, 201)
            except PermissionError as error:
                self._send_json({"error": str(error)}, 403)
            except ValueError as error:
                self._send_json({"error": str(error)}, 400)
            except OSError as error:
                print(f"麻将 CSV 写入失败: {error}")
                self._send_json({"error": "无法写入麻将牌局记录"}, 500)
            return
        if self.path != "/api/admin/games":
            self._send_json({"error": "没有找到接口"}, 404)
            return
        try:
            self._require_admin()
            data = self._read_json()
            human_count = data.get("human_count", 3)
            if isinstance(human_count, str) and human_count.isdecimal():
                human_count = int(human_count)
            game = SERVICE.create_game(str(data.get("title", "")), human_count)
            forwarded_proto = self.headers.get("X-Forwarded-Proto", "http").split(",")[0]
            host = self.headers.get("Host", f"localhost:{PORT}")
            game["invite_url"] = (
                f"{forwarded_proto}://{host}/?game=landlord"
                f"&room={game['game_id']}"
            )
            self._send_json({"game": game}, 201)
        except PermissionError as error:
            self._send_json({"error": str(error)}, 403)
        except ValueError as error:
            self._send_json({"error": str(error)}, 400)
        except OSError as error:
            print(f"CSV 写入失败: {error}")
            self._send_json({"error": "无法写入牌局 CSV，请检查接收端目录权限"}, 500)

    def do_DELETE(self) -> None:
        path = urlparse(self.path).path
        if path == "/api/admin/session":
            try:
                self._require_admin()
                token = self.headers.get("X-Admin-Token", "")
                clear_admin_session(token)
                self._send_json({"logged_out": True})
            except PermissionError as error:
                self._send_json({"error": str(error)}, 403)
            return
        if path == "/api/admin/csv/rooms":
            try:
                self._require_admin()
                data = self._read_json()
                game_ids = data.get("game_ids")
                if not isinstance(game_ids, list):
                    raise ValueError("房间编号列表格式无效")
                self._send_json(SERVICE.delete_csv_rooms(game_ids))
            except PermissionError as error:
                self._send_json({"error": str(error)}, 403)
            except ValueError as error:
                self._send_json({"error": str(error)}, 400)
            return
        if path.startswith("/api/mahjong/admin/games/"):
            try:
                self._require_admin()
                game_id = path.rsplit("/", 1)[-1]
                self._send_json({
                    "game": MAHJONG_SERVICE.close_game(game_id)
                })
            except PermissionError as error:
                self._send_json({"error": str(error)}, 403)
            except ValueError as error:
                self._send_json({"error": str(error)}, 404)
            except OSError as error:
                print(f"关闭麻将房间失败: {error}")
                self._send_json({"error": "关闭麻将牌局记录失败"}, 500)
            return
        csv_room_prefix = "/api/admin/csv/rooms/"
        if path.startswith(csv_room_prefix):
            try:
                self._require_admin()
                game_id = path[len(csv_room_prefix):]
                if not game_id or "/" in game_id:
                    raise ValueError("房间编号无效")
                self._send_json(SERVICE.delete_csv_room(game_id))
            except PermissionError as error:
                self._send_json({"error": str(error)}, 403)
            except ValueError as error:
                self._send_json({"error": str(error)}, 400)
            except OSError as error:
                print(f"CSV 房间数据删除失败: {error}")
                self._send_json({"error": "无法安全更新 CSV，请检查文件状态和目录权限"}, 500)
            except csv.Error as error:
                print(f"CSV 格式错误: {error}")
                self._send_json({"error": "CSV 文件格式错误，无法安全删除房间数据"}, 500)
            return
        csv_prefix = "/api/admin/csv/"
        if path.startswith(csv_prefix):
            try:
                self._require_admin()
                record_id = path[len(csv_prefix):]
                game_id, separator, event_no_text = record_id.partition("/")
                if not separator or not event_no_text.isdecimal():
                    raise ValueError("牌局编号或记录序号无效")
                result = SERVICE.delete_csv_event(game_id, int(event_no_text))
                self._send_json(result)
            except PermissionError as error:
                self._send_json({"error": str(error)}, 403)
            except ValueError as error:
                self._send_json({"error": str(error)}, 400)
            except OSError as error:
                print(f"CSV 记录删除失败: {error}")
                self._send_json({"error": "无法安全更新 CSV，请检查文件状态和目录权限"}, 500)
            except csv.Error as error:
                print(f"CSV 格式错误: {error}")
                self._send_json({"error": "CSV 文件格式错误，无法安全删除记录"}, 500)
            return
        prefix = "/api/admin/games/"
        if not path.startswith(prefix):
            self._send_json({"error": "没有找到接口"}, 404)
            return
        try:
            self._require_admin()
            game = SERVICE.close_game(path[len(prefix):])
            self._send_json({"game": game})
        except PermissionError as error:
            self._send_json({"error": str(error)}, 403)
        except ValueError as error:
            self._send_json({"error": str(error)}, 404)
        except OSError as error:
            print(f"关闭房间时 CSV 写入失败: {error}")
            self._send_json({"error": "关闭记录写入 CSV 失败，请检查接收端目录权限"}, 500)

    def _serve_file(self, path: Path) -> None:
        try:
            body = path.read_bytes()
        except OSError as error:
            print(f"页面读取失败 ({path}): {error}")
            self._send_json({"error": "页面文件读取失败"}, 500)
            return
        self._headers(200, "text/html; charset=utf-8", len(body))
        self.wfile.write(body)

    def _read_exact(self, count: int) -> bytes:
        data = self.rfile.read(count)
        if len(data) != count:
            raise ConnectionError("WebSocket 连接已关闭")
        return data

    def _read_frame(self) -> tuple[int, bytes]:
        first, second = self._read_exact(2)
        opcode = first & 0x0F
        masked = bool(second & 0x80)
        length = second & 0x7F
        if length == 126:
            length = struct.unpack("!H", self._read_exact(2))[0]
        elif length == 127:
            length = struct.unpack("!Q", self._read_exact(8))[0]
        if length > 65536:
            raise ValueError("WebSocket 消息过大")
        if not masked:
            raise ValueError("客户端 WebSocket 消息必须掩码")
        mask = self._read_exact(4)
        payload = self._read_exact(length)
        return opcode, bytes(value ^ mask[index % 4]
                             for index, value in enumerate(payload))

    def send_json(self, data: dict[str, Any]) -> None:
        body = json.dumps(data, ensure_ascii=False).encode("utf-8")
        with self._send_lock:
            self.wfile.write(websocket_frame(body))
            self.wfile.flush()

    def _websocket(self) -> None:
        is_mahjong = urlparse(self.path).path == "/ws/mahjong"
        key = self.headers.get("Sec-WebSocket-Key", "")
        if not key or self.headers.get("Upgrade", "").lower() != "websocket":
            self._send_json({"error": "WebSocket 握手无效"}, 400)
            return
        accept = base64.b64encode(
            hashlib.sha1((key + WS_GUID).encode("ascii")).digest()
        ).decode("ascii")
        self.send_response(101, "Switching Protocols")
        self.send_header("Upgrade", "websocket")
        self.send_header("Connection", "Upgrade")
        self.send_header("Sec-WebSocket-Accept", accept)
        self.end_headers()
        self.close_connection = True
        self._send_lock = threading.Lock()
        current: tuple[str, str] | None = None
        try:
            while True:
                opcode, payload = self._read_frame()
                if opcode == 8:
                    break
                if opcode == 9:
                    with self._send_lock:
                        self.wfile.write(websocket_frame(payload, opcode=10))
                        self.wfile.flush()
                    continue
                if opcode != 1:
                    continue
                try:
                    message = json.loads(payload.decode("utf-8"))
                    if not isinstance(message, dict):
                        raise ValueError("消息必须是 JSON 对象")
                    service = MAHJONG_SERVICE if is_mahjong else SERVICE
                    current = service.handle_message(self, message, current)
                except (json.JSONDecodeError, UnicodeDecodeError, ValueError) as error:
                    self.send_json({"type": "error", "message": str(error)})
        except (ConnectionError, OSError, socket.timeout):
            pass
        finally:
            if current:
                service = MAHJONG_SERVICE if is_mahjong else SERVICE
                service.unregister_client(current[0], current[1], self)
                service.broadcast(current[0])

    def do_OPTIONS(self) -> None:
        self.send_response(204)
        self.send_header("Allow", "GET, POST, OPTIONS")
        self.end_headers()

    def do_PUT(self) -> None:
        self._send_json({"error": "不支持的请求"}, 405)

    def do_PATCH(self) -> None:
        self._send_json({"error": "不支持的请求"}, 405)

    def handle_one_request(self) -> None:
        self._send_lock = threading.Lock()
        super().handle_one_request()

class LandlordHTTPServer(ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = True


def main() -> None:
    try:
        CSV_PATH.touch(exist_ok=True)
        MAHJONG_SERVICE.csv_path.touch(exist_ok=True)
    except OSError as error:
        raise RuntimeError(f"无法创建牌局 CSV 文件: {error}") from error
    server = LandlordHTTPServer((HOST, PORT), RequestHandler)
    print(f"棋牌接收端已启动: http://127.0.0.1:{PORT}")
    print(f"游戏大厅: http://127.0.0.1:{PORT}/")
    print(f"管理页面: http://127.0.0.1:{PORT}/admin")
    print(f"管理口令: {ADMIN_PASSWORD}")
    print(f"斗地主 CSV: {CSV_PATH}")
    print(f"湖南麻将 CSV: {MAHJONG_SERVICE.csv_path}")
    print("Cloudflare Tunnel 命令: cloudflared tunnel --url "
          f"http://127.0.0.1:{PORT}")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n接收端已停止")
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
