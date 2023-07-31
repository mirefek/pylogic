import curses
from annotated_term import *
from thibault import ThibaultEnv, SimpRewriter
import itertools
from calc_numbers import MathNumber
from term import BVar
from line_edit import LineEdit
from lexer import ErrorInLine

class ThibaultTui:
    def __init__(self, stdscr, tenv, term):

        curses.start_color()
        curses.use_default_colors()

        # prepare AnnotatedTerm
        self.tenv = tenv
        self.aterm = AnnotatedTerm(
            term.substitute_free({tenv.X : BVar(1)}),
            bound_names = ['X']
        )
        self.aterm.add_notation()
        self.aterm.link_bvars()
        self.aterm.notation.auto_split_lines(60)

        # evaluate on first 20 elements
        self.aterm.add_calc_term(tenv.calculator)
        for n in range(20):
            self.aterm.calc_term.evaluate([MathNumber(n)])

        # prepare TUI
        self.scr = stdscr
        curses.curs_set(False)
        self.hl_subterm = self.aterm
        self.hl_path = set((self.hl_subterm,))
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
            elif isinstance(part, ATNBinder):
                if hl_indent is not None: attr = self.hl_bvar_color_pair
                elif aterm.subterms[part.ai] in self.hl_path:
                    attr = self.fvar_color_pair
                else: attr = self.bvar_color_pair
            elif isinstance(part, ATNBvar):
                if aterm.bvar_link is None or aterm.bvar_link in self.hl_path:
                    if hl_indent is None: attr = self.fvar_color_pair
                    else: attr = self.hl_fvar_color_pair
                else:
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
            if isinstance(part, ATNSubterm):
                self.display_aterm(aterm.subterms[part.ai], hl_indent = hl_indent)
            else:
                self.scr.addstr(str(part), attr)

    def display_calc_cache(self, aterm):
        cache = aterm.calc_term.cache
        cur_y,_ = self.scr.getyx()
        max_y,_ = self.scr.getmaxyx()
        start_y = cur_y+2

        # collect header
        used_vars = [aterm.bound_names[-i] for i in aterm.calc_term.used_bvars]

        # collect data
        num_rows = min(len(cache), max_y - start_y-1)
        if not num_rows: return

        rows = [
            [str(x) for x in args]+[str(value)]
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
            for col,size,name in zip(cols, col_sizes, used_vars+['value'])
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
                attrs = [self.fvar_color_pair]*len(used_vars) + [0]
            else: attrs = [0]*len(row)
            self.scr.move(start_y+i, 0)
            for j,(x,attr) in enumerate(zip(row, attrs)):
                self.scr.addstr('  ')
                self.scr.addstr(x, attr)

    def loop(self):
        self._running = True
        while self._running:
            self.scr.move(0, 0)
            self.display_aterm(self.aterm)
            self.display_calc_cache(self.hl_subterm)
            key = self.scr.getkey()
            self.on_key(key)
            self.scr.clear()

    def on_key(self, key):
        y,x = self.scr.getmaxyx()
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
                self.hl_path.add(self.hl_subterm)
        elif key == 'KEY_UP':
            if self.hl_subterm.parent is not None:
                self.down_ids.append(self.hl_subterm.parent_i)
                self.hl_path.remove(self.hl_subterm)
                self.hl_subterm = self.hl_subterm.parent
        elif key == 'KEY_LEFT':
            if self.hl_subterm.parent is not None:
                i = self.hl_subterm.parent_i
                parent = self.hl_subterm.parent
                if i > 0:
                    self.down_ids = []
                    self.hl_path.remove(self.hl_subterm)
                    self.hl_subterm = parent.subterms[i-1]
                    self.hl_path.add(self.hl_subterm)
        elif key == 'KEY_RIGHT':
            if self.hl_subterm.parent is not None:
                i = self.hl_subterm.parent_i
                parent = self.hl_subterm.parent
                if i < len(parent.subterms)-1:
                    self.down_ids = []
                    self.hl_path.remove(self.hl_subterm)
                    self.hl_subterm = parent.subterms[i+1]
                    self.hl_path.add(self.hl_subterm)
        elif key == '\n':
            self.irewrite()

    def irewrite(self):
        scr_height, scr_width = self.scr.getmaxyx()
        def show_err(err):
            scr_height, scr_width = self.scr.getmaxyx()
            self.scr.move(scr_height-4-err.count('\n'), 0)
            self.scr.addstr('\n')
            self.scr.addstr(err+'\n')
            self.scr.addstr('\n')

        line_edit = LineEdit(self.scr)
        while True:
            line_edit._set_cursor()
            res = line_edit.loop()
            if res is None or res.strip() == '': break
            try:
                term = self.tenv.env.parser.parse_str(
                    res,
                    local_context = self.hl_subterm.bound_names,
                    available_vars = ()
                )
                if not (term.bound_vars <= self.hl_subterm.term.bound_vars):
                    extra_bvars = sorted(term.bound_vars - self.hl_subterm.term.bound_vars)
                    extra_bvars = [self.hl_subterm.bound_names[-x] for x in extra_bvars]
                    extra_bvars.reverse()
                    extra_bvars = ' '.join(extra_bvars)
                    show_err(f"Extra bound variables not supported (yet):\n  {extra_bvars}")
                    continue

                aterm = AnnotatedTerm(term, bound_names = self.hl_subterm.bound_names)
                aterm.add_calc_term(tenv.calculator)

                failed = False
                args = [None]*len(self.hl_subterm.bound_names)
                cterm0 = self.hl_subterm.calc_term
                cterm1 = aterm.calc_term
                for key, value0 in cterm0.cache.items():
                    for i,x in zip(cterm0.used_bvars, key):
                        args[-i] = x
                    value1 = cterm1.evaluate(args)
                    if value0 != value1:
                        input_vars = ' '.join(str(x) for x in key)
                        show_err(f"Inconsistent value\n  {input_vars}\n  ori = {value0}, new = {value1}")
                        failed = True
                        break
                if failed: continue

                # exchange in the term
                aterm.new_bound_names = self.hl_subterm.new_bound_names
                if self.hl_subterm == self.aterm: self.aterm = aterm
                else: self.hl_subterm.parent.replace_subterm(self.hl_subterm.parent_i, aterm)

                self.hl_path.remove(self.hl_subterm)
                self.hl_subterm = aterm
                self.hl_path.add(self.hl_subterm)
                aterm.add_notation()
                for x in aterm.path_to_root(): x.notation.calculate_str()
                aterm.link_bvars()
                self.aterm.notation.auto_split_lines(60)
                self.down_ids = []
                break
            except Exception as e:
                if isinstance(e, ErrorInLine):
                    show_err(str(e.msg))
                    line_edit.cursor = e.start
                else:
                    raise
                    show_err(str(e))

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

    def make_term_kolakoski():
        line = "C C L C G C C D H B E A K C H A K N L C G M C C D H B E A K C H A K N L C G M C C D H B E A K C H A K N L C G M C C D H B E A K C H A K N L C G M C C D H B E A K C H A K N L C G M C C D H B E A K C H A K N L C G M C C D H B E A K C H A K N K M E C G C H E"
        term = tenv.letters_to_seq_program(line.split())
        return term

    def make_term2():
        term = tenv.env.parser.parse_str("""
        sum(1 .. X, b : if b % 4 = 0 || (b % 4 = 3 && ! ((1 + X) % b = 0)) ; 1 else if b % 4 = 3 || (b % 4 = 1 && (1 + X) % b = 0) ; 0 else - 1) + 1
        """)
        return term

    def make_term_primes():
        return tenv.env.parser.parse_str("""
        loop(X,1,
          x:y: loop(x,x,
            x:y: (if (x % y) = 0 || x % 2 = 0; x+1 else x)
          )
        )
        """)

    curses.wrapper(ThibaultTui, tenv, make_term_motzkin())
