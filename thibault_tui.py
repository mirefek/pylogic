import curses
from annotated_term import AnnotatedTerm
from thibault import ThibaultEnv, SimpRewriter
import itertools

class ThibaultTui:
    def __init__(self, stdscr, tenv, term):

        curses.start_color()
        curses.use_default_colors()

        # prepare AnnotatedTerm
        self.tenv = tenv
        self.aterm = AnnotatedTerm(term)
        self.aterm.add_notation()
        self.aterm.notation.auto_split_lines()

        # evaluate on first 20 elements
        self.tenv.add_calc_term(self.aterm)
        for n in range(20):
            self.tenv.eval_aterm(self.aterm, n)

        # prepare TUI
        self.scr = stdscr
        curses.curs_set(False)
        self.hl_subterm = self.aterm
        self.init_color_pairs()
        self.down_ids = []

        self.loop()

    def init_color_pairs(self):
        color_fvar = curses.COLOR_YELLOW
        color_bvar = curses.COLOR_CYAN
        curses.init_pair(1, color_bvar, curses.COLOR_BLACK)
        self.bvar_color_pair = curses.color_pair(1)
        curses.init_pair(2, color_fvar, curses.COLOR_BLACK)
        self.fvar_color_pair = curses.color_pair(2)

        #curses.init_color(0, 500, 500, 500)
        color_bg = curses.COLOR_BLUE
        color_bg = 238
        
        curses.init_pair(3, curses.COLOR_WHITE, color_bg)
        self.hl_color_pair = curses.color_pair(3)
        curses.init_pair(4, color_bvar, color_bg)
        self.hl_bvar_color_pair = curses.color_pair(4)
        curses.init_pair(5, color_fvar, color_bg)
        self.hl_fvar_color_pair = curses.color_pair(5)

    def display_aterm(self, aterm, hl_indent = None):
        if aterm == self.hl_subterm:
            _, hl_indent = self.scr.getyx()
        atn = aterm.notation
        for i,part in enumerate(atn.parts):
            if hl_indent is None: attr = 0
            else: attr = self.hl_color_pair
            if i == 0 and aterm.term.is_free_var:
                if hl_indent is None: attr = self.fvar_color_pair
                else: attr = self.hl_fvar_color_pair
            elif isinstance(part, (tuple, int)):
                if hl_indent is None: attr = self.bvar_color_pair
                else: attr = self.hl_bvar_color_pair
            if i > 0:
                space_lines = atn.spaces[i-1].split('\n')
                for si,spaces in enumerate(space_lines):
                    if si > 0: self.scr.addstr('\n')
                    if si > 0 and hl_indent is not None:
                        if hl_indent > len(spaces): hl_indent = len(spaces)
                        self.scr.addstr(spaces[:hl_indent])
                        self.scr.addstr(spaces[hl_indent:], attr)
                    else:
                        self.scr.addstr(spaces, attr)
            if isinstance(part, AnnotatedTerm):
                self.display_aterm(part, hl_indent = hl_indent)
            else:
                self.scr.addstr(atn.part_to_str(part), attr)

    def display_calc_cache(self, aterm):
        cache = aterm.calc_term.cache
        cur_y,_ = self.scr.getyx()
        max_y,_ = self.scr.getmaxyx()
        start_y = cur_y+2

        # collect header
        fvs = [(fv.name, True) for fv in aterm.calc_fvs]
        bvs = [(name,False) for name in aterm.bound_names]
        n = len(fvs) + len(bvs)
        used_vars = [
            name for i,name in enumerate(fvs+bvs)
            if aterm.calc_term.used_bvars & (1 << (n-i-1))
        ]

        # collect data
        num_rows = min(len(cache), max_y - start_y-1)
        if not num_rows: return

        rows = [
            [str(x) for x in reversed(args)]+[str(value)]
            for args, value in itertools.islice(cache.items(), num_rows)
        ]
        cols = list(zip(*rows))

        def pad_left(x, size):
            return ' '*(size-len(x)) + x
        def pad_center(x,size):
            spaces = size-len(x)
            spaces1 = spaces // 2
            spaces0 = spaces - spaces1
            return ' '*spaces0 + x + ' '*spaces1
        # align numbers left
        col_sizes = [max(len(x) for x in col) for col in cols]
        cols = [
            [name]+[pad_left(x,size) for x in col]
            for col,size,(name,_) in zip(cols, col_sizes, used_vars+[('value',0)])
        ]
        # align header to center
        col_sizes = [max(len(x) for x in col) for col in cols]
        cols = [
            [pad_center(x,size) for x in col]
            for col,size in zip(cols, col_sizes)
        ]
        rows = list(zip(*cols))

        for i, row in enumerate(rows):
            if i == 0:
                attrs = [
                    [self.bvar_color_pair, self.fvar_color_pair][is_free]
                    for _,is_free in used_vars
                ]+[0]
            else: attrs = [0]*len(row)
            self.scr.move(start_y+i, 0)
            for j,(x,attr) in enumerate(zip(row, attrs)):
                self.scr.addstr('  ')
                self.scr.addstr(x, attr)
        return

        self.scr.move(cur_y, 0)
        for name,is_free in used_vars:
            if is_free: attr = self.fvar_color_pair
            else: attr = self.bvar_color_pair
            self.scr.addstr(name+' ', attr)
        cur_y += 1
        for args, value in cache.items():
            args = [str(x) for x in args]
            value = str(value)
            if cur_y >= max_y: break
            self.scr.addstr(cur_y, 0, f"{args} -> {value}")
            cur_y += 1

    def loop(self):
        self._running = True
        while self._running:
            self.scr.move(0, 0)
            self.display_aterm(self.aterm)
            self.display_calc_cache(self.hl_subterm)
            key = self.scr.getkey()
            self.scr.clear()        
            self.on_key(key)

    def on_key(self, key):
        y,x = self.scr.getmaxyx()
        self.scr.addstr(y-1,x-len(repr(key))-1,repr(key))
        if key in ('q', '\x1b'):
            self._running = False
        elif key == 'KEY_DOWN':
            if self.hl_subterm.subterms:
                if self.down_ids:
                    self.hl_subterm = self.hl_subterm.subterms[self.down_ids.pop()]
                else:
                    self.hl_subterm = max(
                        self.hl_subterm.subterms,
                        key = lambda aterm: len(str(aterm))
                    )
        elif key == 'KEY_UP':
            if self.hl_subterm.parent is not None:
                self.down_ids.append(self.hl_subterm.parent_i)
                self.hl_subterm = self.hl_subterm.parent
        elif key == 'KEY_LEFT':
            if self.hl_subterm.parent is not None:
                i = self.hl_subterm.parent_i
                parent = self.hl_subterm.parent
                if i > 0:
                    self.down_ids = []
                    self.hl_subterm = parent.subterms[i-1]
        elif key == 'KEY_RIGHT':
            if self.hl_subterm.parent is not None:
                i = self.hl_subterm.parent_i
                parent = self.hl_subterm.parent
                if i < len(parent.subterms)-1:
                    self.down_ids = []
                    self.hl_subterm = parent.subterms[i+1]

if __name__ == "__main__":
    import os
    os.environ['TERM'] = 'xterm-256color'

    tenv = ThibaultEnv()
    def make_term_motzkin():
        line = "B C D K L F F C L D G K D K L K E L A I E C K B C C D D G D K J K L F B L D A K K A B L D I E C K B C C D D G D K J E B B K L K E L A I E C K B C C D D G D K J D N J K L F A K K A B L D I E C K B C C D D G D K J E B J G B L J K E B L D K B B K K F K D C G D N"
        term = tenv.letters_to_seq_program(line.split())
        rewriter = tenv.env.rewriter
        simp_rewriter = SimpRewriter(tenv)
        term = rewriter.run(term, simp_rewriter, repeat = True).term[1]
        term = rewriter.run(term, tenv.env.constants.let).term[1]
        term = rewriter.run(term, simp_rewriter, repeat = True).term[1]
        return term

    def make_term2():
        term = tenv.env.parser.parse_str("""
        sum(1 .. X, b : if b % 4 = 0 || (b % 4 = 3 && ! ((1 + X) % b = 0)) ; 1 else if b % 4 = 3 || (b % 4 = 1 && (1 + X) % b = 0) ; 0 else - 1) + 1
        """)
        return term
    curses.wrapper(ThibaultTui, tenv, make_term_motzkin())
