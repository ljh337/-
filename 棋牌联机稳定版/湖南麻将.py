import json
import random
import tkinter as tk
from tkinter import ttk, messagebox
from collections import Counter
from pathlib import Path


SUITS = ('万', '条', '筒')
SUIT_COLORS = ('#b52b2b', '#176b47', '#235aa0')
TILE_NAMES = tuple(f'{rank + 1}{SUITS[suit]}' for suit in range(3) for rank in range(9))
ALL_TILES = [suit * 9 + rank for suit in range(3) for rank in range(9) for _ in range(4)]
TABLE_BG = '#0a5c36'
PANEL_BG = '#084d2c'
PLAYER_NAMES = ('你', '电脑 B', '电脑 C', '电脑 D')


def tile_name(tile):
    return TILE_NAMES[tile]


def get_opening_patterns(hand):
    if len(hand) != 14:
        return set()
    if any(count > 4 for count in Counter(hand).values()):
        return set()
    patterns = set()
    if not any(tile % 9 + 1 in (2, 5, 8) for tile in hand):
        patterns.add('板板胡')
    if len({tile // 9 for tile in hand}) < 3:
        patterns.add('缺一色')
    counts = Counter(hand)
    if any(count == 4 for count in counts.values()):
        patterns.add('四喜')
    if sum(count >= 3 for count in counts.values()) >= 2:
        patterns.add('六六顺')
    return patterns


def get_win_patterns(hand, meld_count=0, exposed_melds=(), meld_open=()):
    """返回长沙常见胡牌类型；番数因地区而异，游戏内只区分大小胡。"""
    if len(hand) != (4 - meld_count) * 3 + 2:
        return set()
    concealed = Counter(hand)
    if any(count > 4 for count in concealed.values()):
        return set()
    full_hand = list(hand) + [tile for meld in exposed_melds for tile in meld]
    patterns = set()
    if (meld_count == 0 and len(hand) == 14
            and all(count % 2 == 0 for count in concealed.values())):
        patterns.add('七小对')
        if any(count == 4 for count in concealed.values()):
            patterns.add('豪华七小对')

    def remove_melds(remaining, needed):
        if needed == 0:
            return (not any(remaining), not any(remaining))
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
        result = remove_melds([concealed[index] for index in range(27)], 4 - meld_count)
        concealed[eye] += 2
        if result and result[0]:
            regular_hand = True
            all_triplet_hand = all_triplet_hand or result[1]
            has_258_eye = has_258_eye or eye % 9 + 1 in (2, 5, 8)
    if not regular_hand:
        return patterns
    if has_258_eye:
        patterns.add('平胡')
    exposed_triplets_only = all(len(set(meld)) == 1 for meld in exposed_melds)
    if all_triplet_hand and exposed_triplets_only:
        patterns.add('碰碰胡')
    if (meld_count == 4 and len(hand) == 2 and len(meld_open) == 4
            and all(meld_open)):
        patterns.add('全求人')
    if len({tile // 9 for tile in full_hand}) == 1:
        patterns.add('清一色')
    if all(tile % 9 + 1 in (2, 5, 8) for tile in full_hand):
        patterns.add('将将胡')
    return patterns


class HunanMahjong:
    def __init__(self, root):
        self.root = root
        self.root.title('湖南麻将')
        self.root.geometry('1100x720')
        self.root.minsize(1000, 680)
        self.root.configure(bg=TABLE_BG)
        try:
            self.root.state('zoomed')
        except tk.TclError:
            pass

        self.hands = [[] for _ in range(4)]
        self.melds = [[] for _ in range(4)]
        self.discards = [[] for _ in range(4)]
        self.scores = [0, 0, 0, 0]
        self.history = []
        self.memory_path = Path(__file__).with_name('湖南麻将记忆.json')
        self.memory_enabled = True
        self._load_memory()
        self.status_text = ''
        self.wall = []
        self.current = 0
        self.last_discard = None
        self.last_discarder = None
        self.discard_pending_resolution = False
        self.selected = None
        self.claim_options = set()
        self.waiting_claim = False
        self.game_over = True
        self.meld_open = [[] for _ in range(4)]
        self.last_draw_was_kong = [False] * 4
        self.last_draw_was_last = [False] * 4
        self.first_discard_pending = True
        self.pending_added_kong = None
        self.claim_extra_patterns = set()
        self.round_id = 0
        self._rules_window = None
        self._build_ui()
        self._show_history()
        self.new_game()
        self.root.bind('<Return>', lambda _event: self.discard_selected())
        self.root.bind('<Escape>', lambda _event: self.pass_action())
        self.root.protocol('WM_DELETE_WINDOW', self.root.destroy)

    def _build_ui(self):
        tk.Label(self.root, text='湖 南 麻 将', font=('楷体', 26, 'bold'),
                 bg=TABLE_BG, fg='gold').pack(pady=6)
        top = tk.Frame(self.root, bg=TABLE_BG)
        top.pack(fill=tk.X, pady=2)
        tk.Label(top, text=PLAYER_NAMES[2], font=('微软雅黑', 10, 'bold'),
                 bg=TABLE_BG, fg='#cfe9d6').pack()
        self.top_canvas = self._canvas(top, height=54)
        self.top_canvas.pack(fill=tk.X)

        middle = tk.Frame(self.root, bg=TABLE_BG)
        middle.pack(expand=True, fill=tk.BOTH)
        left = tk.Frame(middle, bg=TABLE_BG, width=105)
        left.pack(side=tk.LEFT, padx=8, fill=tk.Y)
        left.pack_propagate(False)
        tk.Label(left, text=PLAYER_NAMES[1], font=('微软雅黑', 10, 'bold'),
                 bg=TABLE_BG, fg='#cfe9d6').pack()
        self.left_canvas = self._canvas(left, width=54)
        self.left_canvas.pack(fill=tk.BOTH, expand=True)

        right = tk.Frame(middle, bg=TABLE_BG, width=225)
        right.pack(side=tk.RIGHT, padx=8, fill=tk.Y)
        right.pack_propagate(False)
        tk.Label(right, text='计  分', font=('微软雅黑', 11, 'bold'),
                 bg=TABLE_BG, fg='gold').pack(pady=(4, 2))
        self.score_label = tk.Label(right, text='', font=('微软雅黑', 10),
                                    bg=PANEL_BG, fg='white', justify=tk.LEFT, anchor='w')
        self.score_label.pack(fill=tk.X, padx=4, pady=2)
        tk.Label(right, text='牌  谱', font=('微软雅黑', 11, 'bold'),
                 bg=TABLE_BG, fg='gold').pack(pady=(8, 2))
        history_frame = tk.Frame(right, bg=TABLE_BG)
        history_frame.pack(fill=tk.BOTH, expand=True, padx=4, pady=2)
        self.history_text = tk.Text(history_frame, width=24, height=12, wrap=tk.WORD,
                                    bg='#062e1a', fg='#d9f2e2', font=('微软雅黑', 9),
                                    relief=tk.FLAT, bd=0, state=tk.DISABLED)
        scrollbar = ttk.Scrollbar(history_frame, command=self.history_text.yview)
        self.history_text.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.history_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        right_seat = tk.Frame(middle, bg=TABLE_BG, width=72)
        right_seat.pack(side=tk.RIGHT, padx=4, fill=tk.Y)
        right_seat.pack_propagate(False)
        tk.Label(right_seat, text=PLAYER_NAMES[3], font=('微软雅黑', 9, 'bold'),
             bg=TABLE_BG, fg='#cfe9d6').pack()
        self.right_canvas = self._canvas(right_seat, width=48)
        self.right_canvas.pack(fill=tk.BOTH, expand=True)

        center = tk.Frame(middle, bg=TABLE_BG)
        center.pack(side=tk.LEFT, expand=True, fill=tk.BOTH)
        tk.Label(center, text='牌  墙', font=('微软雅黑', 10, 'bold'),
                 bg=TABLE_BG, fg='gold').pack()
        self.wall_canvas = self._canvas(center, height=62)
        self.wall_canvas.pack(fill=tk.X, pady=2)
        tk.Label(center, text='本轮出牌', font=('微软雅黑', 10, 'bold'),
                 bg=TABLE_BG, fg='gold').pack()
        self.center_canvas = self._canvas(center, height=220)
        self.center_canvas.pack(fill=tk.BOTH, expand=True, pady=2)
        self.rule_panel = tk.Frame(center, bg='#062e1a',
                                   highlightbackground='#d7b84b', highlightthickness=1)
        self.rule_panel.place(relx=1.0, rely=0.0, x=-6, y=6, anchor='ne')
        self.rule_button = tk.Label(self.rule_panel, text='玩法说明', font=('微软雅黑', 9, 'bold'),
                                    bg='#15663c', fg='#FFD700', padx=8, pady=2, cursor='hand2')
        self.rule_button.pack(fill=tk.X)
        self.rule_button.bind('<Button-1>', self._toggle_rules)

        tk.Label(self.root, text='你', font=('微软雅黑', 10, 'bold'),
                 bg=TABLE_BG, fg='#cfe9d6').pack()
        self.player_canvas = self._canvas(self.root, height=124)
        self.player_canvas.pack(fill=tk.X, pady=5)
        self.player_canvas.bind('<Button-1>', self._click_hand)
        self.player_canvas.bind('<Configure>', lambda _event: self.refresh())
        bar = tk.Frame(self.root, bg=TABLE_BG)
        bar.pack(pady=4)
        style = ttk.Style()
        try:
            style.theme_use('clam')
        except tk.TclError:
            pass
        style.configure('Mahjong.TButton', font=('微软雅黑', 10, 'bold'), padding=7,
                        background='#15663c', foreground='white')
        style.map('Mahjong.TButton', background=[('active', '#1c8a55'), ('disabled', '#3a3a3a')])
        self.btn_discard = ttk.Button(bar, text='打出选中牌', command=self.discard_selected,
                                      style='Mahjong.TButton')
        self.btn_hu = ttk.Button(bar, text='胡', command=self.hu, style='Mahjong.TButton')
        self.btn_peng = ttk.Button(bar, text='碰', command=self.peng, style='Mahjong.TButton')
        self.btn_gang = ttk.Button(bar, text='杠', command=self.gang, style='Mahjong.TButton')
        self.btn_pass = ttk.Button(bar, text='过', command=self.pass_action, style='Mahjong.TButton')
        self.btn_new = ttk.Button(bar, text='新一局', command=self.new_game, style='Mahjong.TButton')
        for button in (self.btn_discard, self.btn_hu, self.btn_peng, self.btn_gang,
                       self.btn_pass, self.btn_new):
            button.pack(side=tk.LEFT, padx=4)
        status_frame = tk.Frame(center, bg='#d7b84b', padx=2, pady=2)
        status_frame.pack(fill=tk.X, padx=18, pady=(4, 8))
        self.status = tk.Label(status_frame, text='', font=('微软雅黑', 13, 'bold'),
                               bg='#123d29', fg='#fff2a6', justify=tk.CENTER,
                               anchor=tk.CENTER, wraplength=560, padx=12, pady=8)
        self.status.pack(fill=tk.X)
        tk.Label(self.root, text='点击手牌可预选  Enter=打牌  有碰/杠/胡时可选择操作或「过」',
                 font=('微软雅黑', 8), bg=TABLE_BG, fg='#7fa890').pack()
        for canvas in (self.top_canvas, self.left_canvas, self.right_canvas,
                       self.wall_canvas, self.center_canvas):
            canvas.bind('<Configure>', lambda _event: self.refresh())

    @staticmethod
    def _canvas(parent, **kwargs):
        return tk.Canvas(parent, bg=PANEL_BG, highlightthickness=0, bd=0, **kwargs)

    def _toggle_rules(self, _event=None):
        if self._rules_window is not None and self._rules_window.winfo_exists():
            self._rules_window.deiconify()
            self._rules_window.lift()
            return
        window = tk.Toplevel(self.root)
        self._rules_window = window
        window.title('湖南长沙麻将 · 玩法说明')
        window.geometry('640x680')
        window.minsize(520, 480)
        window.configure(bg=TABLE_BG)
        window.transient(self.root)

        body = tk.Frame(window, bg=TABLE_BG)
        body.pack(fill=tk.BOTH, expand=True, padx=12, pady=12)
        text = tk.Text(body, wrap=tk.WORD, bg='#062e1a', fg='#e4f0e6',
                       font=('微软雅黑', 10), relief=tk.FLAT, bd=0,
                       padx=14, pady=12, spacing1=2, spacing3=4)
        scrollbar = ttk.Scrollbar(body, command=text.yview)
        text.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        text.insert('1.0',
            '【玩法定位】\n'
            '本程序采用长沙麻将常见牌型制作单机简化版。湖南各地、不同平台在吃牌、起手胡和计番方面有差异；本说明以程序实际执行的规则为准。\n\n'
            '【牌具与人数】\n'
            '四人游戏，共108张牌：万、条、筒各有1至9，每种4张。不使用东南西北、中发白，也没有花牌。当前简化版每局固定由你坐庄并先打牌，起手14张；三家电脑各13张，牌墙剩55张。\n\n'
            '【一局怎么进行】\n'
            '庄家先打牌；之后按座次轮流摸牌、打牌。别人打出的牌先检查接炮胡，再检查碰或杠；电脑会自动选择可胡牌型。牌墙摸完仍无人胡牌，本局流局。第一位胡牌后本局立即结束，不采用一炮多响或血战到底。\n\n'
            '【吃、碰、杠】\n'
            '本版不能吃牌。别人打出的牌，如果你有两张相同牌，可以碰；有三张相同牌，可以明杠。碰牌后直接打出一张，不再摸牌。手中四张相同牌可以暗杠；已碰的刻子摸到第四张，可以加杠。杠后从牌墙补一张。加杠时其他玩家可以抢杠胡；杠分暂未计算。\n\n'
            '【普通胡牌】\n'
            '标准牌型为四组面子加一对将。面子可以是同花色连续三张的顺子，或三张相同的刻子。小胡要求将牌为二、五、八中的一对。你摸到胡牌张可以自摸；别人打出胡牌张可以接炮。\n\n'
            '【特殊胡牌】\n'
            '起手胡只检查庄家起手14张：板板胡（没有二、五、八）、缺一色（缺少一种花色）、六六顺（至少两个刻子）、四喜（有四张相同牌）。天胡为庄家起手牌已组成普通胡牌。\n'
            '杠上开花：杠后补牌组成胡牌。抢杠胡：其他玩家加杠的牌正好使你胡牌。海底捞月：摸牌墙最后一张后自摸；河底捞鱼：最后一张摸牌被打出后接炮。地胡：庄家打出第一张牌后，闲家接炮胡。\n\n'
            '【本版识别的大胡】\n'
            '清一色：整手牌及副露均为同一花色。\n'
            '碰碰胡：四组面子全是刻子或杠。\n'
            '将将胡：所有牌的点数都是二、五、八。\n'
            '七小对：没有副露，手牌组成七对；含四张相同牌时另标为豪华七小对。\n'
            '全求人：四组副露均为明碰/明杠，手中只剩一对将。大胡按任意对子作将；七小对和大胡不要求258将。\n\n'
            '【计分】\n'
            '本版小胡1分、大胡6分；天胡、地胡、杠上开花、抢杠胡、海底、河底按大胡处理。自摸时其余三家各支付对应分数；接炮时由放铳者支付。分数跨局及重启程序后累计，牌谱也会保留；数据保存在程序同目录的「湖南麻将记忆.json」中。不叠加多种大胡，也不计算杠分。各地规则番数差异较大，此处只是简化计分。\n\n'
            '【地区玩法差异】\n'
            '部分玩法还包含扎鸟、节节高、三同、一只鸟、庄家轮换，以及可吃牌或不同番数算法；本版暂未加入。这里的缺一色是长沙起手胡，不是四川麻将要求整局先打完一门的「定缺」。电脑玩家会自动摸打，并在满足胡牌条件时自动胡牌。')
        text.config(state=tk.DISABLED)

        def close_rules():
            self._rules_window = None
            window.destroy()

        ttk.Button(window, text='关闭', command=close_rules,
                   style='Mahjong.TButton').pack(pady=(0, 12))
        window.protocol('WM_DELETE_WINDOW', close_rules)

    def _set_status(self, text):
        self.status_text = text
        self.status.config(text=text)

    def new_game(self):
        self.round_id += 1
        self.wall = ALL_TILES.copy()
        random.shuffle(self.wall)
        self.hands = [[] for _ in range(4)]
        self.melds = [[] for _ in range(4)]
        self.discards = [[] for _ in range(4)]
        for player in range(4):
            self.hands[player] = [self.wall.pop() for _ in range(14 if player == 0 else 13)]
        self.current = 0
        self.last_discard = None
        self.last_discarder = None
        self.discard_pending_resolution = False
        self.selected = None
        self.claim_options = set()
        self.waiting_claim = False
        self.game_over = False
        self.meld_open = [[] for _ in range(4)]
        self.last_draw_was_kong = [False] * 4
        self.last_draw_was_last = [False] * 4
        self.last_discard_was_last = False
        self.first_discard_pending = True
        self.dealer = 0
        self.pending_added_kong = None
        self.claim_extra_patterns = set()
        self._set_status('新局开始，你先打出一张牌。')
        self.refresh()
        opening_patterns = get_opening_patterns(self.hands[0])
        regular_patterns = get_win_patterns(self.hands[0])
        initial_patterns = opening_patterns | regular_patterns
        if regular_patterns:
            initial_patterns.add('天胡')
        if initial_patterns:
            self._award_win(0, self.hands[0], True, initial_patterns)

    def _click_hand(self, event):
        if self.waiting_claim or self.game_over:
            return
        hand = sorted(self.hands[0])
        if not hand:
            return
        width = max(self.player_canvas.winfo_width(), 700)
        spacing = max(30, min(58, (width - 68) // max(1, len(hand) - 1)))
        start = max(10, (width - ((len(hand) - 1) * spacing + 48)) // 2)
        hit_indices = [index for index in range(len(hand))
                       if start + index * spacing <= event.x <= start + index * spacing + 48]
        if not hit_indices:
            return
        self.selected = max(hit_indices)
        self.refresh()

    def _selected_tile(self):
        hand = sorted(self.hands[0])
        if self.selected is not None and 0 <= self.selected < len(hand):
            return hand[self.selected]
        return None

    def _select_after_draw(self, previous_selection, drawn_tile):
        hand = sorted(self.hands[0])
        tile = previous_selection if previous_selection in hand else drawn_tile
        self.selected = max(index for index, value in enumerate(hand) if value == tile)

    @staticmethod
    def _draw_back(canvas, x, y, width=22, height=34):
        canvas.create_rectangle(x, y, x + width, y + height, fill='#315f9a',
                                outline='#bfd0e3', width=1)
        canvas.create_rectangle(x + 3, y + 3, x + width - 3, y + height - 3,
                                outline='#bfd0e3', width=1)

    def _draw_tile(self, canvas, tile, x, y, width=48, height=64, selected=False):
        canvas.create_rectangle(x + 2, y + 3, x + width + 2, y + height + 3,
                                fill='#04351f', outline='')
        canvas.create_rectangle(x, y, x + width, y + height,
                                fill='#ffe7a0' if selected else '#fffdf4',
                                outline='#e69727' if selected else '#b6aa8f',
                                width=2 if selected else 1)
        canvas.create_text(x + width / 2, y + height / 2, text=tile_name(tile),
                           fill=SUIT_COLORS[tile // 9], font=('微软雅黑', 17, 'bold'))

    def refresh(self):
        if not hasattr(self, 'player_canvas'):
            return
        for canvas in (self.player_canvas, self.top_canvas, self.left_canvas,
                       self.right_canvas, self.wall_canvas, self.center_canvas):
            canvas.delete('all')
        self._draw_player_hand()
        self._draw_opponent(1, self.left_canvas, True)
        self._draw_opponent(2, self.top_canvas, False)
        self._draw_opponent(3, self.right_canvas, True)
        self._draw_wall()
        self._draw_center()
        self.score_label.config(text='\n'.join(
            f'{PLAYER_NAMES[i]}  {score:+d}' for i, score in enumerate(self.scores)))
        self._update_buttons()
        self._sync_status()

    def _sync_status(self):
        if self.game_over:
            text = self.status_text
        elif self.waiting_claim:
            actions = '、'.join(
                {'hu': '胡', 'peng': '碰', 'gang': '杠'}[action]
                for action in ('hu', 'peng', 'gang') if action in self.claim_options)
            if self.pending_added_kong is not None:
                text = f'有人加杠 {tile_name(self.last_discard)}，你可以抢杠胡或过。'
            else:
                text = f'别人打出 {tile_name(self.last_discard)}：可{actions}，也可过。'
        elif self.discard_pending_resolution:
            text = (f'{PLAYER_NAMES[self.last_discarder]}打出 '
                    f'{tile_name(self.last_discard)}，正在检查其他玩家的响应。')
        elif self.current == 0 and len(self.hands[0]) % 3 == 2:
            actions = ['打牌']
            if get_win_patterns(self.hands[0], len(self.melds[0]),
                                self.melds[0], self.meld_open[0]):
                actions.append('自摸胡')
            counts = Counter(self.hands[0])
            can_kong = any(count == 4 for count in counts.values()) or any(
                len(meld) == 3 and counts[meld[0]] for meld in self.melds[0])
            if can_kong:
                actions.append('杠')
            text = f'轮到你出牌。可{"、".join(actions)}。'
        elif self.current == 0:
            text = '轮到你摸牌。'
        else:
            text = f'轮到{PLAYER_NAMES[self.current]}摸牌并出牌。'
        self.status_text = text
        self.status.config(text=text)

    def _draw_player_hand(self):
        canvas = self.player_canvas
        hand = sorted(self.hands[0])
        if not hand:
            return
        width = max(canvas.winfo_width(), 700)
        spacing = max(30, min(58, (width - 68) // max(1, len(hand) - 1)))
        start = max(10, (width - ((len(hand) - 1) * spacing + 48)) // 2)
        for index, tile in enumerate(hand):
            self._draw_tile(canvas, tile, start + index * spacing, 24,
                            height=72, selected=index == self.selected)

    def _draw_opponent(self, player, canvas, vertical):
        count = len(self.hands[player])
        if vertical:
            canvas.create_text(8, 10, text=f'{count}张', fill='gold',
                               font=('微软雅黑', 10, 'bold'), anchor='nw')
            for index in range(min(count, 11)):
                self._draw_back(canvas, 12, 34 + index * 19, 30, 25)
        else:
            canvas.create_text(8, 8, text=f'{count}张', fill='gold',
                               font=('微软雅黑', 9, 'bold'), anchor='nw')
            show = min(count, 24)
            width = max(canvas.winfo_width(), 420)
            for index in range(show):
                self._draw_back(canvas, max(50, (width - show * 16) // 2) + index * 16,
                                22, 20, 30)
        if self.melds[player]:
            text = ' '.join('[' + ' '.join(tile_name(tile) for tile in meld) + ']'
                            for meld in self.melds[player])
            canvas.create_text(8, 58 if not vertical else 250, text=text,
                               fill='#e7d59a', font=('微软雅黑', 8), anchor='nw')

    def _draw_wall(self):
        canvas = self.wall_canvas
        width = max(canvas.winfo_width(), 500)
        canvas.create_text(12, 10, text=f'剩余 {len(self.wall)} 张', fill='gold',
                           font=('微软雅黑', 10, 'bold'), anchor='nw')
        for index in range(min(20, len(self.wall))):
            self._draw_back(canvas, width / 2 - 190 + index * 19, 16, 17, 32)

    def _draw_center(self):
        canvas = self.center_canvas
        width = max(canvas.winfo_width(), 500)
        if self.last_discard is not None:
            canvas.create_text(width / 2, 16, text=f'{PLAYER_NAMES[self.last_discarder]} 打出',
                               fill='#d9f2e2', font=('微软雅黑', 10))
            self._draw_tile(canvas, self.last_discard, width / 2 - 24, 26)
        for player, discards in enumerate(self.discards):
            if discards:
                text = f'{PLAYER_NAMES[player]}：' + ' '.join(
                    tile_name(tile) for tile in discards[-10:])
                canvas.create_text(12, 100 + player * 22, text=text,
                                   fill='#d9f2e2', font=('微软雅黑', 9), anchor='w')
        exposed = [f'{PLAYER_NAMES[player]}：' + ' '.join(
            '[' + ' '.join(tile_name(tile) for tile in meld) + ']'
            for meld in self.melds[player]) for player in range(4) if self.melds[player]]
        if exposed:
            canvas.create_text(12, 194, text='\n'.join(exposed), fill='#f1d98d',
                               font=('微软雅黑', 9), anchor='nw')

    def _update_buttons(self):
        player_turn = self.current == 0 and not self.game_over
        can_discard = player_turn and not self.waiting_claim and len(self.hands[0]) % 3 == 2
        can_hu = 'hu' in self.claim_options or (
            can_discard and bool(get_win_patterns(
                self.hands[0], len(self.melds[0]), self.melds[0], self.meld_open[0])))
        can_add_kong = any(
            len(meld) == 3 and self.hands[0].count(meld[0]) >= 1
            for meld in self.melds[0])
        can_kong = 'gang' in self.claim_options or (
            can_discard and (any(count == 4 for count in Counter(self.hands[0]).values())
                             or can_add_kong))
        self.btn_discard.config(state=tk.NORMAL if can_discard else tk.DISABLED)
        self.btn_hu.config(state=tk.NORMAL if can_hu else tk.DISABLED)
        if self.waiting_claim and 'hu' in self.claim_options:
            self.btn_hu.config(text='接炮胡')
        elif can_hu:
            self.btn_hu.config(text='自摸胡')
        else:
            self.btn_hu.config(text='胡')
        self.btn_peng.config(state=tk.NORMAL if 'peng' in self.claim_options else tk.DISABLED)
        self.btn_gang.config(state=tk.NORMAL if can_kong else tk.DISABLED)
        self.btn_pass.config(state=tk.NORMAL if self.waiting_claim else tk.DISABLED)

    def discard_selected(self):
        if self.current != 0 or self.waiting_claim or self.game_over:
            return
        if len(self.hands[0]) % 3 != 2:
            self._set_status('当前不能打牌。')
            return
        if self.selected is None or not 0 <= self.selected < len(self.hands[0]):
            self._set_status('请先点击选择一张手牌。')
            return
        tile = sorted(self.hands[0])[self.selected]
        self.hands[0].remove(tile)
        self.discards[0].append(tile)
        self._after_discard(0, tile)

    def _after_discard(self, player, tile):
        self.last_discard = tile
        self.last_discarder = player
        self.discard_pending_resolution = True
        self.last_discard_was_last = self.last_draw_was_last[player]
        self.last_draw_was_last[player] = False
        self.last_draw_was_kong[player] = False
        self.selected = None
        self._set_status(
            f'{PLAYER_NAMES[player]}打出 {tile_name(tile)}，正在检查其他玩家的响应。')
        self.refresh()
        self._schedule_round(350, lambda: self._resolve_discard(player, tile))

    def _resolve_discard(self, discarder, tile):
        self.discard_pending_resolution = False
        is_first_discard = self.first_discard_pending and discarder == self.dealer
        self.first_discard_pending = False
        order = [(discarder + offset) % 4 for offset in range(1, 4)]
        for player in order:
            patterns = get_win_patterns(self.hands[player] + [tile], len(self.melds[player]),
                                        self.melds[player], self.meld_open[player])
            extras = set()
            if is_first_discard and player != discarder:
                extras.add('地胡')
            if self.last_discard_was_last:
                extras.add('河底捞鱼')
            if patterns:
                if player == 0:
                    self._ask_claim(tile, {'hu'}, extras)
                else:
                    self._award_win(player, self.hands[player] + [tile], False, extras)
                return
        claims = []
        for player in order:
            copies = self.hands[player].count(tile)
            if copies >= 3:
                claims.append((player, 'gang'))
            elif copies >= 2:
                claims.append((player, 'peng'))
        for player, action in claims:
            if player == 0:
                options = {'peng'} if action == 'gang' else set()
                options.add(action)
                self._ask_claim(tile, options)
                return
            self._claim(player, action, tile)
            return
        self._advance(discarder)

    def _ask_claim(self, tile, options, extra_patterns=()):
        self.waiting_claim = True
        self.claim_options = options
        self.claim_extra_patterns = set(extra_patterns)
        actions = '、'.join({'hu': '胡', 'peng': '碰', 'gang': '杠'}[item]
                           for item in ('hu', 'peng', 'gang') if item in options)
        self._set_status(f'别人打出 {tile_name(tile)}：可{actions}，也可过。')
        self.refresh()

    def _claim(self, player, action, tile):
        copies = 3 if action == 'gang' else 2
        for _ in range(copies):
            self.hands[player].remove(tile)
        self.melds[player].append([tile] * (copies + 1))
        self.meld_open[player].append(True)
        self.current = player
        if player == 0:
            self.selected = None
        self.last_discard = None
        self.last_discarder = None
        self.waiting_claim = False
        self.claim_options.clear()
        self.claim_extra_patterns.clear()
        self._set_status(f'{PLAYER_NAMES[player]}{action} {tile_name(tile)}。')
        self.refresh()
        if action == 'gang':
            self._schedule_round(400, lambda: self._replacement_draw(player))
        elif player == 0:
            self._set_status('碰牌后打出一张手牌。')
        else:
            self._schedule_round(450, lambda: self._ai_turn(player))

    def peng(self):
        if self.waiting_claim and 'peng' in self.claim_options:
            self._claim(0, 'peng', self.last_discard)

    def gang(self):
        if self.waiting_claim and 'gang' in self.claim_options:
            self._claim(0, 'gang', self.last_discard)
            return
        if self.current != 0 or self.game_over or len(self.hands[0]) % 3 != 2:
            return
        counts = Counter(self.hands[0])
        tile = next((value for value, count in counts.items() if count == 4), None)
        if tile is not None:
            for _ in range(4):
                self.hands[0].remove(tile)
            self.melds[0].append([tile] * 4)
            self.meld_open[0].append(False)
            self._set_status(f'暗杠 {tile_name(tile)}，补一张牌。')
            self._replacement_draw(0)
            return
        for meld_index, meld in enumerate(self.melds[0]):
            if len(meld) == 3 and self.hands[0].count(meld[0]):
                self._begin_added_kong(0, meld[0], meld_index)
                return
        self._set_status('当前没有可开的杠。')

    def _begin_added_kong(self, player, tile, meld_index):
        self.pending_added_kong = (player, tile, meld_index)
        self.last_discard = tile
        self.last_discarder = player
        for other in ((player + offset) % 4 for offset in range(1, 4)):
            patterns = get_win_patterns(
                self.hands[other] + [tile], len(self.melds[other]),
                self.melds[other], self.meld_open[other])
            if not patterns:
                continue
            if other == 0:
                self._ask_claim(tile, {'hu'}, {'抢杠胡'})
            else:
                self._award_win(other, self.hands[other] + [tile], False, {'抢杠胡'})
            return
        self._complete_added_kong()

    def _complete_added_kong(self):
        if self.pending_added_kong is None:
            return
        player, tile, meld_index = self.pending_added_kong
        self.hands[player].remove(tile)
        self.melds[player][meld_index].append(tile)
        self.pending_added_kong = None
        self.last_discard = None
        self.last_discarder = None
        self.current = player
        self._set_status(f'{PLAYER_NAMES[player]}加杠 {tile_name(tile)}，补一张牌。')
        self.refresh()
        self._replacement_draw(player)

    def _replacement_draw(self, player):
        if not self.wall:
            self._finish_round('流局')
            return
        previous_selection = self._selected_tile() if player == 0 else None
        self.hands[player].append(self.wall.pop())
        self.last_draw_was_kong[player] = True
        self.last_draw_was_last[player] = not self.wall
        if player == 0:
            self.current = 0
            self._select_after_draw(previous_selection, self.hands[0][-1])
            self._set_status('杠后补牌，请打牌或胡牌。')
            self.refresh()
        else:
            self._ai_turn(player)

    def hu(self):
        if self.waiting_claim and 'hu' in self.claim_options:
            self._award_win(0, self.hands[0] + [self.last_discard], False,
                            self.claim_extra_patterns)
        elif self.current == 0:
            patterns = get_win_patterns(self.hands[0], len(self.melds[0]),
                                        self.melds[0], self.meld_open[0])
            if patterns:
                if self.last_draw_was_kong[0]:
                    patterns.add('杠上开花')
                if self.last_draw_was_last[0]:
                    patterns.add('海底捞月')
                self._award_win(0, self.hands[0], True, patterns)

    def pass_action(self):
        if not self.waiting_claim:
            return
        discarder = self.last_discarder
        self.waiting_claim = False
        self.claim_options.clear()
        self.claim_extra_patterns.clear()
        if self.pending_added_kong is not None:
            self._complete_added_kong()
            return
        self._set_status('你选择过牌。')
        self._advance(discarder)

    def _advance(self, player):
        self.current = (player + 1) % 4
        if not self.wall:
            self._finish_round('流局')
        elif self.current == 0:
            self._set_status('轮到你摸牌。')
            self._schedule_round(250, self._draw_for_human)
        else:
            next_player = self.current
            self._set_status(f'轮到{PLAYER_NAMES[next_player]}摸牌并出牌。')
            self._schedule_round(450, lambda: self._ai_turn(next_player))

    def _schedule_round(self, delay, callback):
        round_id = self.round_id
        self.root.after(
            delay,
            lambda: callback() if round_id == self.round_id else None)

    def _draw_for_human(self):
        if self.game_over or self.current != 0:
            return
        previous_selection = self._selected_tile()
        self.hands[0].append(self.wall.pop())
        tile = self.hands[0][-1]
        self._select_after_draw(previous_selection, tile)
        self.last_draw_was_kong[0] = False
        self.last_draw_was_last[0] = not self.wall
        patterns = get_win_patterns(self.hands[0], len(self.melds[0]),
                                    self.melds[0], self.meld_open[0])
        if patterns:
            if self.last_draw_was_last[0]:
                patterns.add('海底捞月')
            self._set_status(f'你摸到 {tile_name(tile)}，可以自摸胡，点击「自摸胡」确认。')
        else:
            self._set_status(f'你摸到 {tile_name(tile)}。')
        self.refresh()

    def _ai_turn(self, player):
        if self.game_over:
            return
        if len(self.hands[player]) % 3 == 1:
            if not self.wall:
                self._finish_round('流局')
                return
            self.hands[player].append(self.wall.pop())
            self.last_draw_was_kong[player] = False
            self.last_draw_was_last[player] = not self.wall
        patterns = get_win_patterns(self.hands[player], len(self.melds[player]),
                                    self.melds[player], self.meld_open[player])
        if patterns:
            if self.last_draw_was_kong[player]:
                patterns.add('杠上开花')
            if self.last_draw_was_last[player]:
                patterns.add('海底捞月')
            self._award_win(player, self.hands[player], True, patterns)
            return
        for meld_index, meld in enumerate(self.melds[player]):
            if len(meld) == 3 and self.hands[player].count(meld[0]):
                self._begin_added_kong(player, meld[0], meld_index)
                return
        counts = Counter(self.hands[player])
        def discard_value(tile):
            neighbors = sum(counts.get(tile + offset, 0) for offset in (-2, -1, 1, 2)
                            if 0 <= tile + offset < 27
                            and (tile + offset) // 9 == tile // 9)
            return (counts[tile] > 1, neighbors, random.random())
        tile = min(self.hands[player], key=discard_value)
        self.hands[player].remove(tile)
        self.discards[player].append(tile)
        self._after_discard(player, tile)

    def _award_win(self, winner, hand, self_draw, extra_patterns=()):
        if self.game_over:
            return
        self.game_over = True
        patterns = get_win_patterns(hand, len(self.melds[winner]),
                        self.melds[winner], self.meld_open[winner])
        patterns.update(extra_patterns)
        big_patterns = {'清一色', '碰碰胡', '将将胡', '七小对', '豪华七小对',
                '全求人', '杠上开花', '抢杠胡', '海底捞月', '河底捞鱼',
                '天胡', '地胡'}
        big = bool(patterns & big_patterns)
        points = 6 if big else 1
        if self_draw:
            self.scores[winner] += points * 3
            for player in range(4):
                if player != winner:
                    self.scores[player] -= points
        else:
            self.scores[winner] += points
            self.scores[self.last_discarder] -= points
        name = '、'.join(sorted(patterns)) or '平胡'
        summary = f'{PLAYER_NAMES[winner]}{"自摸" if self_draw else "点炮胡"}：{name}（{points}分）'
        self.history.append(summary)
        self._save_memory()
        self._set_status(summary + '。点击「新一局」继续。')
        self._show_history()
        self.refresh()
        messagebox.showinfo('本局结束', summary)

    def _finish_round(self, reason):
        self.game_over = True
        self.history.append(reason)
        self._save_memory()
        self._set_status(f'{reason}。点击「新一局」继续。')
        self._show_history()
        self.refresh()

    def _show_history(self):
        self.history_text.config(state=tk.NORMAL)
        self.history_text.delete('1.0', tk.END)
        if self.history:
            self.history_text.insert(tk.END, '\n'.join(self.history) + '\n')
        self.history_text.see(tk.END)
        self.history_text.config(state=tk.DISABLED)

    def _load_memory(self):
        try:
            data = json.loads(self.memory_path.read_text(encoding='utf-8'))
            if not isinstance(data, dict):
                raise ValueError('记忆文件内容格式错误。')
            scores = data.get('scores')
            history = data.get('history')
            if (not isinstance(scores, list) or len(scores) != 4
                    or any(type(score) is not int for score in scores)):
                raise ValueError('记忆文件中的计分数据格式错误。')
            if (not isinstance(history, list)
                    or any(not isinstance(entry, str) for entry in history)):
                raise ValueError('记忆文件中的牌谱数据格式错误。')
        except FileNotFoundError:
            return
        except (OSError, json.JSONDecodeError, ValueError) as exc:
            self.memory_enabled = False
            messagebox.showerror(
                '读取记忆失败',
                f'无法读取记忆文件：\n{self.memory_path}\n\n{exc}\n\n'
                '本次运行将使用空白计分，且不会覆盖该文件。')
            return
        self.scores = scores
        self.history = history

    def _save_memory(self):
        if not self.memory_enabled:
            return
        data = {'scores': self.scores, 'history': self.history}
        temporary_path = self.memory_path.with_suffix('.tmp')
        try:
            temporary_path.write_text(
                json.dumps(data, ensure_ascii=False, indent=2) + '\n',
                encoding='utf-8')
            temporary_path.replace(self.memory_path)
        except OSError as exc:
            self.memory_enabled = False
            messagebox.showerror(
                '保存记忆失败',
                f'无法保存计分和牌谱：\n{self.memory_path}\n\n{exc}\n\n'
                '本次运行将继续，但后续记录不会保存。')


if __name__ == '__main__':
    window = tk.Tk()
    game = HunanMahjong(window)
    window.mainloop()