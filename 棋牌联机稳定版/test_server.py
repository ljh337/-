import csv
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import call, patch

import web_server
from web_server import (
    ADMIN_PASSWORD,
    GameService,
    can_beat,
    clear_admin_session,
    choose_ai_play,
    create_admin_session,
    detect_combination,
    get_possible_plays,
    make_deck,
    sort_hand,
)


class AdminSessionTests(unittest.TestCase):
    def setUp(self):
        clear_admin_session(web_server.ADMIN_SESSION_TOKEN)

    def tearDown(self):
        clear_admin_session(web_server.ADMIN_SESSION_TOKEN)

    def test_only_one_admin_device_can_be_online_until_logout(self):
        first_session = create_admin_session(ADMIN_PASSWORD)

        with self.assertRaisesRegex(PermissionError, "已有设备在线"):
            create_admin_session(ADMIN_PASSWORD)
        with self.assertRaisesRegex(PermissionError, "管理口令错误"):
            create_admin_session("incorrect password")

        self.assertEqual(web_server.ADMIN_SESSION_TOKEN, first_session)
        clear_admin_session("stale-session")
        self.assertEqual(web_server.ADMIN_SESSION_TOKEN, first_session)

        clear_admin_session(first_session)
        second_session = create_admin_session(ADMIN_PASSWORD)
        self.assertNotEqual(second_session, first_session)


class GameRulesTests(unittest.TestCase):
    def test_deck_has_54_unique_cards(self):
        deck = make_deck()
        self.assertEqual(len(deck), 54)
        self.assertEqual(len({card["id"] for card in deck}), 54)

    def test_hand_sort_uses_rank_then_explicit_suit_order(self):
        deck = make_deck()
        hand = [deck[index] for index in (51, 3, 16, 0, 52, 1, 2, 53)]

        sorted_hand = sort_hand(hand)

        self.assertEqual(
            [card["label"] for card in sorted_hand],
            ["3♠", "3♥", "3♣", "3♦", "7♠", "2♦", "小王", "大王"],
        )

    def test_supported_combinations_and_beating(self):
        self.assertEqual(detect_combination([3, 4, 5, 6, 7]),
                         ("straight", 7, 5))
        self.assertEqual(detect_combination([7, 7, 8, 8, 9, 9]),
                         ("straight_pairs", 9, 6))
        self.assertEqual(detect_combination([16, 17]), ("rocket", 99, 2))
        self.assertTrue(can_beat(("pair", 8, 2), ("pair", 9, 2)))
        self.assertFalse(can_beat(("straight", 8, 5), ("straight", 9, 6)))
        self.assertTrue(can_beat(("single", 14, 1), ("bomb", 5, 4)))

    def test_all_documented_combinations_are_recognized(self):
        cases = [
            ([3], "single"),
            ([3, 3], "pair"),
            ([3, 3, 3], "triple"),
            ([3, 3, 3, 4], "triple_one"),
            ([3, 3, 3, 4, 4], "triple_two"),
            ([3, 4, 5, 6, 7], "straight"),
            ([3, 3, 4, 4, 5, 5], "straight_pairs"),
            ([3, 3, 3, 4, 4, 4], "plane"),
            ([3, 3, 3, 4, 4, 4, 5, 6], "plane_single"),
            ([3, 3, 3, 4, 4, 4, 5, 5, 6, 6], "plane_pairs"),
            ([8, 8, 8, 8], "bomb"),
            ([8, 8, 8, 8, 3, 4], "four_two_single"),
            ([8, 8, 8, 8, 3, 3, 4, 4], "four_two_pairs"),
            ([16, 17], "rocket"),
        ]
        for cards, expected_type in cases:
            with self.subTest(cards=cards):
                result = detect_combination(cards)
                self.assertIsNotNone(result)
                self.assertEqual(result[0], expected_type)

    def test_invalid_sequences_and_attachment_shapes_are_rejected(self):
        invalid_hands = [
            [3, 4, 5, 6],
            [3, 4, 5, 6, 15],
            [3, 3, 4, 4, 6, 6],
            [3, 3, 4, 4, 5, 5, 15, 15],
            [3, 3, 3, 5, 5, 5, 6, 7],
            [3, 3, 3, 5, 5, 5, 6, 6, 7, 7],
            [3, 3, 3, 4, 4, 4, 5],
            [8, 8, 8, 8, 3, 4, 5],
            [8, 8, 8, 8, 3, 3, 4, 4, 5, 5],
        ]
        for cards in invalid_hands:
            with self.subTest(cards=cards):
                self.assertIsNone(detect_combination(cards))

    def test_comparison_obeys_type_length_and_bomb_order(self):
        self.assertTrue(can_beat(("single", 14, 1), ("single", 15, 1)))
        self.assertFalse(can_beat(("pair", 14, 2), ("triple", 3, 3)))
        self.assertFalse(can_beat(("straight", 10, 5), ("straight", 12, 6)))
        self.assertTrue(can_beat(("triple_one", 8, 4), ("triple_one", 9, 4)))
        self.assertTrue(can_beat(("pair", 15, 2), ("bomb", 3, 4)))
        self.assertTrue(can_beat(("bomb", 14, 4), ("bomb", 15, 4)))
        self.assertFalse(can_beat(("bomb", 15, 4), ("bomb", 14, 4)))
        self.assertFalse(can_beat(("rocket", 99, 2), ("bomb", 15, 4)))
        self.assertTrue(can_beat(("bomb", 15, 4), ("rocket", 99, 2)))

    def test_ai_generated_plays_match_combination_validator(self):
        representative_hands = [
            [3, 3, 3, 4, 4, 4, 5, 6, 7, 8, 8, 8, 8, 9, 9, 10, 10],
            [3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 16, 17],
        ]
        for values in representative_hands:
            with self.subTest(values=values):
                for _, _, cards in get_possible_plays(values):
                    self.assertIsNotNone(detect_combination(cards), cards)

    def test_ai_selects_a_legal_play(self):
        deck = make_deck()
        hand = [card for card in deck if card["value"] in (3, 4, 5, 6, 7)]
        selected = choose_ai_play(hand, None)
        self.assertIsNotNone(selected)
        selected_cards = [card for card in hand if card["id"] in selected]
        self.assertIsNotNone(detect_combination(
            [card["value"] for card in selected_cards]
        ))

    def test_ai_leads_with_largest_available_non_bomb_combination(self):
        deck = make_deck()
        hand = [
            next(card for card in deck if card["value"] == value)
            for value in (3, 4, 5, 6, 7)
        ]

        selected = choose_ai_play(hand, None)

        self.assertEqual(len(selected), 5)
        selected_cards = [card for card in hand if card["id"] in selected]
        self.assertEqual(
            detect_combination([card["value"] for card in selected_cards])[0],
            "straight",
        )


class GameServiceTests(unittest.TestCase):
    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.csv_path = Path(self.temp_dir.name) / "games.csv"
        self.service = GameService(self.csv_path)

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_game_can_choose_one_human_and_fills_other_seats_with_ai(self):
        game = self.service.create_game("单人练习", human_count=1)
        self.assertEqual(game["human_count"], 1)
        self.assertEqual(len(game["players"]), 3)
        self.assertEqual(sum(not player["human"] for player in game["players"]), 2)
        joined = self.service.join_game(game["game_id"], "玩家甲")
        self.assertEqual(self.service.games[game["game_id"]]["players"][0]["name"],
                         "玩家甲")

    def test_join_rejects_long_or_computer_like_player_names(self):
        game = self.service.create_game("昵称校验", human_count=1)
        invalid_names = (
            "123456789", "电脑1", "AI玩家", "机器人甲", "系统", "玩家 Bot",
        )
        for name in invalid_names:
            with self.subTest(name=name), self.assertRaises(ValueError):
                self.service.join_game(game["game_id"], name)

        joined = self.service.join_game(game["game_id"], "真人玩家")
        self.assertTrue(joined["token"])
        self.assertEqual(
            self.service.games[game["game_id"]]["players"][0]["name"],
            "真人玩家",
        )

    def test_ai_waits_for_the_action_notice_interval_before_each_move(self):
        game = self.service.create_game("电脑出牌延迟", human_count=1)
        self.service.join_game(game["game_id"], "真人玩家")
        state = self.service.games[game["game_id"]]
        self.service._deal(state)
        state["phase"] = "playing"
        state["current_turn"] = 1
        initial_event_no = state["event_no"]

        with patch.object(web_server.time, "sleep") as sleep, \
                patch.object(self.service, "broadcast"):
            self.service._run_ai_turns(game["game_id"])

        self.assertEqual(
            sleep.call_args_list,
            [
                call(web_server.AI_ACTION_DELAY_SECONDS),
                call(web_server.AI_ACTION_DELAY_SECONDS),
            ],
        )
        self.assertEqual(state["event_no"], initial_event_no + 2)

    def test_ai_waits_for_the_full_landlord_card_reveal(self):
        game = self.service.create_game("电脑等待底牌", human_count=2)
        self.service.join_game(game["game_id"], "真人玩家甲")
        self.service.join_game(game["game_id"], "真人玩家乙")
        state = self.service.games[game["game_id"]]
        self.service._deal(state)
        state["phase"] = "playing"
        state["current_turn"] = 2
        state["landlord_reveal_until"] = 1003

        with patch.object(web_server.time, "time", return_value=1000), \
                patch.object(web_server.time, "sleep") as sleep, \
                patch.object(self.service, "broadcast"):
            self.service._run_ai_turns(game["game_id"])

        sleep.assert_called_once_with(web_server.LANDLORD_REVEAL_SECONDS)

    def test_three_human_round_deals_and_accepts_moves(self):
        game = self.service.create_game("测试桌", human_count=3)
        game_id = game["game_id"]
        players = [
            self.service.join_game(game_id, f"玩家{seat + 1}")
            for seat in range(3)
        ]
        for player in players:
            self.service.action(game_id, player["token"], "ready")

        state = self.service.games[game_id]
        self.assertEqual(state["phase"], "bidding")
        self.assertEqual(sorted(len(player["hand"]) for player in state["players"]),
                         [17, 17, 17])
        state["bid_turn"] = 0
        self.service.action(game_id, players[0]["token"], "bid")
        self.service.action(game_id, players[1]["token"], "not_rob")
        self.service.action(game_id, players[2]["token"], "not_rob")
        self.assertEqual(state["phase"], "playing")
        self.assertEqual(state["landlord"], 0)
        self.assertEqual(len(state["players"][0]["hand"]), 20)

        card_id = state["players"][0]["hand"][0]["id"]
        self.service.action(game_id, players[0]["token"], "play",
                            {"card_ids": [card_id]})
        self.assertEqual(state["last_play"]["seat"], 0)
        self.assertEqual(state["current_turn"], 1)
        self.service.action(game_id, players[1]["token"], "pass")
        self.assertEqual(state["current_turn"], 2)

    def test_dealt_hands_and_landlord_hand_are_sorted(self):
        game = self.service.create_game("排序测试", human_count=3)
        game_id = game["game_id"]
        players = [
            self.service.join_game(game_id, f"排序玩家{seat + 1}")
            for seat in range(3)
        ]
        for player in players:
            self.service.action(game_id, player["token"], "ready")

        state = self.service.games[game_id]
        self.assertTrue(all(
            player["hand"] == sort_hand(player["hand"])
            for player in state["players"]
        ))
        state["bid_turn"] = 0
        self.service.action(game_id, players[0]["token"], "bid")
        self.service.action(game_id, players[1]["token"], "not_rob")
        self.service.action(game_id, players[2]["token"], "not_rob")
        landlord = state["players"][state["landlord"]]
        self.assertEqual(landlord["hand"], sort_hand(landlord["hand"]))

    def test_player_can_rob_landlord_and_all_pass_redeals(self):
        game = self.service.create_game("抢地主测试", human_count=3)
        game_id = game["game_id"]
        players = [
            self.service.join_game(game_id, f"抢地主玩家{seat + 1}")
            for seat in range(3)
        ]
        for player in players:
            self.service.action(game_id, player["token"], "ready")
        state = self.service.games[game_id]
        state["bid_turn"] = 0

        self.service.action(game_id, players[0]["token"], "bid")
        self.assertEqual(state["bid_candidate"], 0)
        self.assertEqual(state["bid_turn"], 1)
        player_view = self.service.player_view(state, players[0]["token"])
        self.assertEqual(player_view["bid_candidate"], 0)
        self.service.action(game_id, players[1]["token"], "rob")
        self.assertEqual(state["phase"], "playing")
        self.assertIsNone(state["bid_turn"])
        self.assertIsNone(state["bid_candidate"])
        self.assertEqual(state["landlord"], 1)
        self.assertEqual(len(state["players"][1]["hand"]), 20)
        with self.assertRaisesRegex(ValueError, "不是叫地主阶段"):
            self.service.action(game_id, players[2]["token"], "rob")

        redeal_game = self.service.create_game("无人叫地主", human_count=3)
        redeal_players = [
            self.service.join_game(redeal_game["game_id"], f"不叫玩家{seat + 1}")
            for seat in range(3)
        ]
        for player in redeal_players:
            self.service.action(redeal_game["game_id"], player["token"], "ready")
        redeal_state = self.service.games[redeal_game["game_id"]]
        redeal_state["bid_turn"] = 0
        for player in redeal_players:
            self.service.action(redeal_game["game_id"], player["token"], "decline")
        self.assertEqual(redeal_state["phase"], "bidding")
        self.assertEqual(redeal_state["bid_count"], 0)
        self.assertIsNone(redeal_state["bid_candidate"])
        self.assertEqual(redeal_state["deal_no"], 2)

    def test_landlord_bottom_cards_are_shared_for_three_seconds(self):
        game = self.service.create_game("底牌公开测试", human_count=3)
        players = [
            self.service.join_game(game["game_id"], f"公开测试{seat + 1}")
            for seat in range(3)
        ]
        state = self.service.games[game["game_id"]]
        self.service._deal(state)
        state["bid_turn"] = 0
        bottom_labels = [card["label"] for card in state["bottom"]]

        self.service.action(game["game_id"], players[0]["token"], "bid")
        self.service.action(game["game_id"], players[1]["token"], "rob")

        for credentials in players:
            view = self.service.player_view(state, credentials["token"])
            self.assertEqual(view["landlord_reveal"]["cards"], bottom_labels)
            self.assertGreater(view["landlord_reveal"]["remaining_ms"], 0)
            self.assertLessEqual(
                view["landlord_reveal"]["remaining_ms"],
                web_server.LANDLORD_REVEAL_SECONDS * 1000,
            )

        state["landlord_reveal_until"] = web_server.time.time() - 1
        self.assertIsNone(
            self.service.player_view(state, players[0]["token"])["landlord_reveal"]
        )
        self.service._deal(state)
        self.assertEqual(state["landlord_reveal_cards"], [])
        self.assertEqual(state["landlord_reveal_until"], 0)

    def test_rematch_requires_every_human_and_reuses_player_identities(self):
        game = self.service.create_game("原玩家再开", human_count=2)
        game_id = game["game_id"]
        credentials = [
            self.service.join_game(game_id, f"再开玩家{seat + 1}")
            for seat in range(2)
        ]
        state = self.service.games[game_id]
        original_ids = [player["id"] for player in state["players"]]
        original_tokens = [player["token"] for player in state["players"]]
        state["phase"] = "finished"
        state["winner"] = 0
        state["round_no"] = 1

        self.service.action(game_id, credentials[0]["token"], "rematch")
        self.assertEqual(state["phase"], "finished")
        self.assertEqual(state["rematch_votes"], [0])
        self.assertIn("1/2", state["message"])

        first_view = self.service.player_view(state, credentials[0]["token"])
        self.assertEqual(first_view["round_no"], 1)
        self.assertEqual(first_view["rematch_votes"], [0])
        restored_vote = GameService(self.csv_path)
        self.assertEqual(
            restored_vote.games[game_id]["rematch_votes"],
            [0],
        )

        self.service.action(game_id, credentials[0]["token"], "rematch")
        self.assertEqual(state["rematch_votes"], [])
        self.assertEqual(state["phase"], "finished")

        self.service.action(game_id, credentials[0]["token"], "rematch")
        self.service.action(game_id, credentials[1]["token"], "rematch")

        self.assertEqual(state["phase"], "bidding")
        self.assertEqual(state["round_no"], 2)
        self.assertEqual(state["deal_no"], 1)
        self.assertEqual(state["rematch_votes"], [])
        self.assertEqual([player["id"] for player in state["players"]], original_ids)
        self.assertEqual([player["token"] for player in state["players"]], original_tokens)
        self.assertTrue(all(len(player["hand"]) == 17 for player in state["players"]))
        self.assertTrue(all(
            player["hand"] == sort_hand(player["hand"])
            for player in state["players"]
        ))
        self.assertTrue(state["players"][2]["ready"])
        self.assertFalse(state["players"][0]["ready"])
        self.assertEqual(state["events"][-1]["action"], "rematch_started")
        self.assertEqual(
            self.service.admin_game(game_id)["round_no"],
            2,
        )

    def test_rematch_vote_is_rejected_before_game_finishes(self):
        game = self.service.create_game("尚未结束不可再开", human_count=1)
        credentials = self.service.join_game(game["game_id"], "再开测试玩家")

        with self.assertRaisesRegex(ValueError, "只有已结束"):
            self.service.action(game["game_id"], credentials["token"], "rematch")

    def test_invalid_card_id_types_are_rejected_cleanly(self):
        game = self.service.create_game("牌编号验证", human_count=3)
        players = [
            self.service.join_game(game["game_id"], f"验证玩家{seat + 1}")
            for seat in range(3)
        ]
        for player in players:
            self.service.action(game["game_id"], player["token"], "ready")
        state = self.service.games[game["game_id"]]
        state["bid_turn"] = 0
        self.service.action(game["game_id"], players[0]["token"], "bid")
        self.service.action(game["game_id"], players[1]["token"], "not_rob")
        self.service.action(game["game_id"], players[2]["token"], "not_rob")

        with self.assertRaisesRegex(ValueError, "编号无效"):
            self.service.action(
                game["game_id"], players[0]["token"], "play",
                {"card_ids": [{"malformed": True}]},
            )

    def test_csv_is_single_append_only_log_and_restores_latest_snapshot(self):
        game = self.service.create_game("恢复测试", human_count=3)
        credentials = self.service.join_game(game["game_id"], "恢复玩家")
        with self.csv_path.open("r", encoding="utf-16", newline="") as file:
            rows = list(csv.DictReader(file))
        self.assertEqual(len(rows), 2)
        self.assertEqual(rows[-1]["action"], "player_joined")

        restored = GameService(self.csv_path)
        restored_game = restored.admin_game(game["game_id"])
        self.assertEqual(restored_game["players"][0]["name"], "恢复玩家")
        self.assertFalse(restored_game["players"][0]["connected"])
        self.assertTrue(credentials["token"])

    def test_csv_viewer_filters_pages_and_redacts_player_credentials(self):
        game = self.service.create_game("查看器测试", human_count=1)
        credentials = self.service.join_game(game["game_id"], "查看玩家")

        first_page = self.service.csv_view(page=1, page_size=2)
        matching = self.service.csv_view(
            page=1, page_size=10, game_id=game["game_id"], query="查看玩家"
        )

        self.assertEqual(first_page["total"], 2)
        self.assertEqual(len(first_page["events"]), 2)
        self.assertEqual(first_page["events"][0]["action"], "player_joined")
        self.assertEqual(first_page["events"][1]["action"], "game_created")
        self.assertEqual(matching["total"], 1)
        self.assertEqual(matching["events"][0]["action_label"], "玩家加入并坐到1号位")
        self.assertEqual(matching["events"][0]["snapshot"]["players"][0]["name"],
                         "查看玩家")
        self.assertNotIn("token", json.dumps(matching, ensure_ascii=False))
        self.assertNotIn(credentials["token"], json.dumps(matching, ensure_ascii=False))

    def test_csv_viewer_rejects_invalid_pagination(self):
        with self.assertRaisesRegex(ValueError, "页码"):
            self.service.csv_view(page=0)
        with self.assertRaisesRegex(ValueError, "每页条数"):
            self.service.csv_view(page_size=101)

    def test_csv_export_contains_full_readable_game_history_without_credentials(self):
        game = self.service.create_game("可读导出测试", human_count=1)
        credentials = self.service.join_game(game["game_id"], "导出玩家")
        state = self.service.games[game["game_id"]]
        self.service._deal(state)
        self.service._write_event(state, "dealt", details={
            "deal_no": state["deal_no"],
            "first_bidder": state["players"][state["bid_turn"]]["name"],
        })
        self.service.create_game("其他房间", human_count=1)

        filename, exported = self.service.export_csv_game(game["game_id"])

        self.assertEqual(filename, f"landlord-game-{game['game_id']}.csv")
        self.assertTrue(exported.startswith(b"\xef\xbb\xbf"))
        exported_text = exported.decode("utf-8-sig")
        self.assertNotIn(credentials["token"], exported_text)
        with io.StringIO(exported_text, newline="") as stream:
            rows = list(csv.DictReader(stream))
        self.assertEqual(len(rows), 3)
        self.assertEqual(
            [row["操作类型"] for row in rows],
            ["创建房间", "玩家加入", "发牌"],
        )
        self.assertEqual(rows[0]["房间名称"], "可读导出测试")
        self.assertEqual(rows[1]["操作玩家"], "导出玩家")
        self.assertEqual(rows[2]["座位1类型"], "真人")
        self.assertEqual(int(rows[2]["座位1剩余牌数"]), 17)
        self.assertTrue(rows[2]["座位1当时手牌"])
        self.assertNotIn("其他房间", exported_text)

    def test_csv_export_rejects_unknown_room(self):
        with self.assertRaisesRegex(ValueError, "没有该牌局的数据"):
            self.service.export_csv_game("MISSING")

    def test_deleting_latest_csv_event_keeps_recoverable_state_checkpoint(self):
        game = self.service.create_game("删除最新记录", human_count=3)
        self.service.join_game(game["game_id"], "保留状态玩家")
        player_id = self.service.games[game["game_id"]]["players"][0]["id"]
        result = self.service.delete_csv_event(game["game_id"], 2)

        self.assertEqual(result, {"deleted": True, "checkpointed": True})
        with self.csv_path.open("r", encoding="utf-16", newline="") as file:
            rows = list(csv.DictReader(file))
        self.assertEqual([row["action"] for row in rows],
                         ["game_created", "state_checkpoint"])
        visible = self.service.csv_view(game_id=game["game_id"])
        self.assertEqual(visible["total"], 1)
        self.assertEqual(visible["events"][0]["action"], "game_created")
        self.assertNotIn(2, [
            event["event_no"]
            for event in self.service.games[game["game_id"]]["events"]
        ])

        restored = GameService(self.csv_path)
        restored_game = restored.admin_game(game["game_id"])
        self.assertEqual(restored_game["players"][0]["name"], "保留状态玩家")
        self.assertEqual(
            restored.games[game["game_id"]]["players"][0]["id"],
            player_id,
        )
        self.assertNotIn(2, [
            event["event_no"]
            for event in restored.games[game["game_id"]]["events"]
        ])

    def test_deleting_older_csv_event_removes_it_from_later_snapshots(self):
        game = self.service.create_game("删除历史记录", human_count=3)
        self.service.join_game(game["game_id"], "后续玩家")
        result = self.service.delete_csv_event(game["game_id"], 1)

        self.assertEqual(result, {"deleted": True, "checkpointed": False})
        with self.csv_path.open("r", encoding="utf-16", newline="") as file:
            rows = list(csv.DictReader(file))
        self.assertEqual([row["action"] for row in rows], ["player_joined"])
        saved_events = json.loads(rows[0]["state_json"])["events"]
        self.assertEqual([event["event_no"] for event in saved_events], [2])
        restored = GameService(self.csv_path)
        self.assertEqual(len(restored.admin_game(game["game_id"])["events"]), 1)

    def test_csv_event_deletion_rejects_missing_or_invalid_records(self):
        game = self.service.create_game("删除记录校验", human_count=3)
        with self.assertRaisesRegex(ValueError, "序号无效"):
            self.service.delete_csv_event(game["game_id"], 0)
        with self.assertRaisesRegex(ValueError, "没有这条记录"):
            self.service.delete_csv_event(game["game_id"], 99)

    def test_csv_viewer_groups_rooms_with_phase_and_record_count(self):
        open_game = self.service.create_game("进行中的房间", human_count=1)
        closed_game = self.service.create_game("已关闭的房间", human_count=1)
        self.service.close_game(closed_game["game_id"])

        result = self.service.csv_view()
        rooms = {room["game_id"]: room for room in result["rooms"]}

        self.assertEqual(rooms[open_game["game_id"]]["phase"], "lobby")
        self.assertEqual(rooms[open_game["game_id"]]["event_count"], 1)
        self.assertEqual(rooms[closed_game["game_id"]]["phase"], "closed")
        self.assertEqual(rooms[closed_game["game_id"]]["event_count"], 2)

    def test_deleting_closed_room_removes_only_its_csv_data(self):
        deleted_game = self.service.create_game("要删除的房间", human_count=1)
        self.service.join_game(deleted_game["game_id"], "删除玩家")
        self.service.close_game(deleted_game["game_id"])
        kept_game = self.service.create_game("保留的房间", human_count=1)

        with self.assertRaisesRegex(ValueError, "只能删除已关闭"):
            self.service.delete_csv_room(kept_game["game_id"])

        result = self.service.delete_csv_room(deleted_game["game_id"])

        self.assertEqual(result["game_id"], deleted_game["game_id"])
        self.assertEqual(result["deleted_rows"], 3)
        self.assertNotIn(deleted_game["game_id"], self.service.games)
        with self.csv_path.open("r", encoding="utf-16", newline="") as file:
            rows = list(csv.DictReader(file))
        self.assertTrue(rows)
        self.assertTrue(all(row["game_id"] == kept_game["game_id"] for row in rows))
        self.assertEqual(
            [room["game_id"] for room in self.service.csv_view()["rooms"]],
            [kept_game["game_id"]],
        )
        restored = GameService(self.csv_path)
        self.assertNotIn(deleted_game["game_id"], restored.games)
        self.assertIn(kept_game["game_id"], restored.games)

    def test_deleting_open_room_data_is_rejected_without_changing_csv(self):
        game = self.service.create_game("不可删除的进行中房间", human_count=1)
        original = self.csv_path.read_bytes()

        with self.assertRaisesRegex(ValueError, "只能删除已关闭"):
            self.service.delete_csv_room(game["game_id"])

        self.assertEqual(self.csv_path.read_bytes(), original)

    def test_batch_delete_removes_selected_closed_rooms_and_preserves_others(self):
        delete_games = [
            self.service.create_game(f"批量删除房间{i}", human_count=1)
            for i in range(2)
        ]
        for game in delete_games:
            self.service.close_game(game["game_id"])
        kept_game = self.service.create_game("批量删除保留", human_count=1)

        result = self.service.delete_csv_rooms([
            game["game_id"] for game in delete_games
        ])

        self.assertEqual(set(result["game_ids"]), {
            game["game_id"] for game in delete_games
        })
        self.assertEqual(result["deleted_rows"], 4)
        self.assertNotIn(delete_games[0]["game_id"], self.service.games)
        self.assertNotIn(delete_games[1]["game_id"], self.service.games)
        self.assertIn(kept_game["game_id"], self.service.games)
        with self.csv_path.open("r", encoding="utf-16", newline="") as file:
            rows = list(csv.DictReader(file))
        self.assertEqual(
            {row["game_id"] for row in rows},
            {kept_game["game_id"]},
        )

    def test_batch_delete_rejects_open_room_without_deleting_closed_rooms(self):
        closed_game = self.service.create_game("批量原子关闭房间", human_count=1)
        self.service.close_game(closed_game["game_id"])
        open_game = self.service.create_game("批量原子进行中", human_count=1)
        original = self.csv_path.read_bytes()

        with self.assertRaisesRegex(ValueError, "尚未关闭"):
            self.service.delete_csv_rooms([
                closed_game["game_id"], open_game["game_id"]
            ])

        self.assertEqual(self.csv_path.read_bytes(), original)
        self.assertIn(closed_game["game_id"], self.service.games)
        self.assertIn(open_game["game_id"], self.service.games)

    def test_admin_api_view_restores_older_snapshots_missing_optional_fields(self):
        game = self.service.create_game("旧版快照", human_count=3)
        with self.csv_path.open("r", encoding="utf-16", newline="") as file:
            rows = list(csv.DictReader(file))
        snapshot = json.loads(rows[-1]["state_json"])
        snapshot.pop("bid_candidate")
        snapshot.pop("bid_count")
        snapshot.pop("human_count")
        snapshot.pop("closed_at")
        for player in snapshot["players"]:
            player.pop("human")
        rows[-1]["state_json"] = json.dumps(snapshot, ensure_ascii=False)
        with self.csv_path.open("w", encoding="utf-16", newline="") as file:
            writer = csv.DictWriter(file, fieldnames=rows[0].keys())
            writer.writeheader()
            writer.writerows(rows)

        restored = GameService(self.csv_path)
        detail = restored.admin_game(game["game_id"])

        self.assertIsNone(detail["bid_candidate"])
        self.assertEqual(detail["human_count"], 3)
        self.assertIsNone(detail["closed_at"])
        self.assertEqual(len(restored.list_games()), 1)

    def test_csv_has_one_excel_compatible_utf16_bom(self):
        game = self.service.create_game("Excel 编码测试", human_count=1)
        self.service.join_game(game["game_id"], "甲")
        content = self.csv_path.read_bytes()
        self.assertTrue(content.startswith(b"\xff\xfe"))
        self.assertEqual(content.count(b"\xff\xfe"), 1)
        with self.csv_path.open("r", encoding="utf-16", newline="") as file:
            rows = list(csv.DictReader(file))
        self.assertEqual(rows[0]["details_json"], '{"title": "Excel 编码测试", "human_count": 1}')

    def test_existing_utf8_csv_is_migrated_without_losing_records(self):
        game = self.service.create_game("旧文件转换", human_count=3)
        with self.csv_path.open("r", encoding="utf-16", newline="") as file:
            original_text = file.read()
        self.csv_path.write_text(original_text, encoding="utf-8")

        restored = GameService(self.csv_path)

        migrated = self.csv_path.read_bytes()
        self.assertTrue(migrated.startswith(b"\xff\xfe"))
        self.assertEqual(migrated.count(b"\xff\xfe"), 1)
        with self.csv_path.open("r", encoding="utf-16", newline="") as file:
            rows = list(csv.DictReader(file))
        self.assertEqual(len(rows), 1)
        self.assertEqual(restored.admin_game(game["game_id"])["title"], "旧文件转换")

    def test_admin_can_close_room_without_removing_history(self):
        game = self.service.create_game("可关闭房间", human_count=1)
        self.assertIsNotNone(game["created_at"])
        self.assertIsNone(game["closed_at"])
        credentials = self.service.join_game(game["game_id"], "管理测试玩家")

        closed = self.service.close_game(game["game_id"])

        self.assertEqual(closed["phase"], "closed")
        self.assertIsNotNone(closed["closed_at"])
        self.assertGreaterEqual(closed["closed_at"], game["created_at"])
        self.assertEqual(closed["message"], "管理员已关闭房间")
        self.assertEqual(closed["events"][-1]["description"], "管理员关闭房间")
        self.assertEqual(len(self.service.list_games()), 1)
        with self.assertRaisesRegex(ValueError, "房间已经关闭"):
            self.service.close_game(game["game_id"])
        with self.assertRaisesRegex(ValueError, "当前阶段"):
            self.service.action(game["game_id"], credentials["token"], "ready")

        restored = GameService(self.csv_path)
        restored_view = restored.admin_game(game["game_id"])
        self.assertEqual(restored_view["phase"], "closed")
        self.assertEqual(restored_view["closed_at"], closed["closed_at"])

    def test_admin_view_explains_turn_and_played_cards(self):
        game = self.service.create_game("易读详情", human_count=3)
        players = [
            self.service.join_game(game["game_id"], f"详情玩家{seat + 1}")
            for seat in range(3)
        ]
        for player in players:
            self.service.action(game["game_id"], player["token"], "ready")
        state = self.service.games[game["game_id"]]
        state["bid_turn"] = 0
        self.service.action(game["game_id"], players[0]["token"], "bid")
        if state["phase"] == "bidding":
            self.service.action(game["game_id"], players[1]["token"], "decline")
            self.service.action(game["game_id"], players[2]["token"], "decline")
        landlord = state["landlord"]
        card = state["players"][landlord]["hand"][0]
        self.service.action(game["game_id"], players[landlord]["token"],
                            "play", {"card_ids": [card["id"]]})

        detail = self.service.admin_game(game["game_id"])

        self.assertEqual(detail["current_player"],
                         state["players"][state["current_turn"]]["name"])
        self.assertIn(card["label"], detail["last_play"]["cards"])
        self.assertTrue(all("description" in event for event in detail["events"]))
        for admin_player, game_player in zip(detail["players"], state["players"]):
            self.assertEqual(
                admin_player["hand"],
                [hand_card["label"] for hand_card in game_player["hand"]],
            )

        player_view = self.service.player_view(
            state, players[landlord]["token"]
        )
        self.assertEqual(
            [hand_card["label"] for hand_card in player_view["hand"]],
            detail["players"][landlord]["hand"],
        )
        self.assertNotIn("hand", player_view["players"][0])

    def test_admin_view_reports_each_lobby_players_ready_state(self):
        game = self.service.create_game("准备状态显示", human_count=2)
        players = [
            self.service.join_game(game["game_id"], f"准备显示玩家{seat + 1}")
            for seat in range(2)
        ]
        self.service.action(game["game_id"], players[0]["token"], "ready")

        detail = self.service.admin_game(game["game_id"])

        self.assertEqual(detail["phase"], "lobby")
        self.assertTrue(detail["players"][0]["ready"])
        self.assertFalse(detail["players"][1]["ready"])
        self.assertTrue(detail["players"][2]["ready"])

    def test_invalid_human_count_is_rejected(self):
        with self.assertRaises(ValueError):
            self.service.create_game(human_count=0)
        with self.assertRaises(ValueError):
            self.service.create_game(human_count=True)


if __name__ == "__main__":
    unittest.main()
