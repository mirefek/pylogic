#!/usr/bin/python3

import curses
from term import next_names
from annotated_term import *
from thibault import ThibaultEnv, SimpRewriter
import itertools
from calc_numbers import MathNumber
from term import BVar
from line_edit import LineEdit
from lexer import ErrorInLine

class ThibaultTui:
    def __init__(self, stdscr, fname, num_eval, right_space = 20):

        start, prev_values = self.load_aterm(fname)

        curses.start_color()
        curses.use_default_colors()

        # prepare AnnotatedTerm
        win_height, win_width = stdscr.getmaxyx()
        self.pp_width = win_width - right_space
        self.aterm.notation.auto_split_lines(self.pp_width)

        with open(fname, 'a') as self.f:

            # evaluate on first num_eval elements
            self.aterm.add_calc_term(self.tenv.calculator)
            seq = []
            for n in range(num_eval):
                seq.append(self.aterm.calc_term.evaluate([MathNumber(n)]))
            assert all(isinstance(x, MathNumber) and x.x % 1 == 0 for x in seq)
            seq = [int(x.x) for x in seq]
            assert all(x == y for x,y in zip(prev_values, seq))

            if len(seq) > len(prev_values):
                self.log("VALUES", ' '.join(map(str, seq)))
            if start: self.log_term()

            # prepare TUI
            self.scr = stdscr
            curses.curs_set(False)
            self.hl_subterm = self.aterm
            self.hl_path = set((self.hl_subterm,))
            self.init_color_pairs()
            self.down_ids = []
            self.subterm_mode = True
            self.cancel_subterm_mode(init = True)

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

        faded_color = 8
        curses.init_pair(6, faded_color, curses.COLOR_BLACK)
        self.faded_color_pair = curses.color_pair(6)

    def load_aterm(self, fname):
        
        with open(fname) as f:
            term_str = None
            values_str = ""
            program = next(f)
            for line in f:
                if ': ' in line:
                    tag, data = line.split(': ', 1)
                    if tag == "TERM": term_str = data
                    elif tag == "VALUES": values_str = data
        self.tenv = ThibaultEnv()
        if term_str is None:
            term = self.tenv.letters_to_seq_program(program.split())
            simp_rewriter = SimpRewriter(self.tenv)
            term = self.tenv.env.rewriter.run(term, simp_rewriter, repeat = True).term[1]
        else:
            term = self.tenv.env.parser.parse_str(term_str)
        term = term.substitute_free({self.tenv.X : BVar(1)})

        self.aterm = AnnotatedTerm(term, bound_names = ['x'])
        self.aterm.add_notation()
        self.aterm.link_bvars()

        values = [int(x) for x in values_str.split()]
        return term_str is None, values

    def display_aterm(self, aterm, hl_indent = None, faded = None):
        if faded is None: faded = self.subterm_mode
        if aterm == self.hl_subterm:
            _, hl_indent = self.scr.getyx()
        atn = aterm.notation
        if aterm == self.unfade: faded = False
        for i,part in enumerate(atn.parts):
            if faded: attr = self.faded_color_pair
            else:
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
                self.display_aterm(aterm.subterms[part.ai], faded = faded, hl_indent = hl_indent)
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

        def value_to_str(value):
            term = self.tenv.calculator.get_value_term(value)
            return str(term)
        rows = [
            [value_to_str(x) for x in args]+[value_to_str(value)]
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

    def display_abstract_term(self):
        cur_y,_ = self.scr.getyx()
        start_y = cur_y+2
        self.scr.move(start_y, 0)
        self.scr.addstr(self.abstract_term.to_str(bound_names = tuple(self.unfade.bound_names)))

    def loop(self):
        self._running = True
        while self._running:
            self.scr.move(0, 0)
            self.display_aterm(self.aterm)
            if not self.subterm_mode:
                self.display_calc_cache(self.hl_subterm)
            else:
                self.display_abstract_term()
            key = self.scr.getkey()
            self.on_key(key)
            self.scr.clear()

    def on_key(self, key):
        y,x = self.scr.getmaxyx()
        if key in ('q', '\x1b'):
            self._running = False
        elif key == 'KEY_DOWN':
            if self.subterm_mode:
                if self.hl_subterm in self.subterm_subterms:
                    self.subterm_subterms.remove(self.hl_subterm)
                    self.subterm_subterms.update(
                        self.hl_subterm.subterms
                    )
                self.update_abstract_term()
            if self.hl_subterm.subterms:
                if self.down_ids:
                    self.hl_subterm = self.hl_subterm.subterms[self.down_ids.pop()]
                else:
                    self.hl_subterm = max(
                        self.hl_subterm.subterms,
                        key = lambda aterm: len(str(aterm))
                    )
                if not self.subterm_mode:
                    self.hl_path.add(self.hl_subterm)
        elif key == 'KEY_UP':
            if self.hl_subterm == self.unfade: self.cancel_subterm_mode()
            if self.hl_subterm.parent is not None:
                self.down_ids.append(self.hl_subterm.parent_i)
                if not self.subterm_mode: self.hl_path.remove(self.hl_subterm)
                self.hl_subterm = self.hl_subterm.parent
        elif key == 'KEY_LEFT':
            if self.hl_subterm == self.unfade: self.cancel_subterm_mode()
            if self.hl_subterm.parent is not None:
                i = self.hl_subterm.parent_i
                parent = self.hl_subterm.parent
                if i > 0:
                    self.down_ids = []
                    if not self.subterm_mode: self.hl_path.remove(self.hl_subterm)
                    self.hl_subterm = parent.subterms[i-1]
                    if not self.subterm_mode: self.hl_path.add(self.hl_subterm)
        elif key == 'KEY_RIGHT':
            if self.hl_subterm.parent is not None:
                if self.hl_subterm == self.unfade: self.cancel_subterm_mode()
                i = self.hl_subterm.parent_i
                parent = self.hl_subterm.parent
                if i < len(parent.subterms)-1:
                    self.down_ids = []
                    if not self.subterm_mode: self.hl_path.remove(self.hl_subterm)
                    self.hl_subterm = parent.subterms[i+1]
                    if not self.subterm_mode: self.hl_path.add(self.hl_subterm)
        elif key == ' ':
            if self.subterm_mode: self.cancel_subterm_mode()
            else: self.start_subterm_mode()
        elif key == '\n':
            self.irewrite()

    def start_subterm_mode(self):
        self.subterm_mode = True
        self.unfade = self.hl_subterm
        self.subterm_subterms = set()
        self.subterm_subterms.add(self.hl_subterm)
        self.update_abstract_term()
    def cancel_subterm_mode(self, init = False, update_path = True):
        if not init:
            if not self.subterm_mode: return
            if update_path:
                x = self.hl_subterm
                while x not in self.hl_path:
                    self.hl_path.add(x)
                    x = x.parent
        self.subterm_mode = False
        self.unfade = None
        self.subterm_subterms = None
        self.abstract_term = None
        self.abstract_term_subst = None
    def update_abstract_term(self):
        names = next_names('A')
        def make_var(arity):
            name = next(names)
            return self.tenv.parser.get_var(name, arity)
        self.abstract_term, self.abstract_term_subst = self.unfade.abstract_subterms(self.subterm_subterms, make_var)

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
                if self.subterm_mode:
                    lhs_str = self.abstract_term.to_str(
                        bound_names = tuple(self.unfade.bound_names)
                    )
                    aterm_ori = self.unfade
                    available_vars = set(self.abstract_term_subst.keys())
                else:
                    lhs_str = self.hl_subterm.term.to_str(
                        bound_names = tuple(self.hl_subterm.bound_names)
                    )
                    aterm_ori = self.hl_subterm
                    available_vars = ()
                term = self.tenv.env.parser.parse_str(
                    res,
                    local_context = aterm_ori.bound_names,
                    available_vars = available_vars,
                )
                rhs_str = term.to_str(bound_names = tuple(aterm_ori.bound_names))
                if self.subterm_mode:
                    term = term.substitute_free(self.abstract_term_subst)
                replaced = aterm_ori.calc_replace(term)
                if self.aterm == aterm_ori:
                    self.aterm = replaced

                self.hl_path.remove(aterm_ori)
                self.hl_subterm = replaced
                self.log("REPLACE", ' '.join(map(str, replaced.path_i())))
                self.log("LHS", lhs_str)
                self.log("RHS", rhs_str)
                self.log_term()
                self.hl_path.add(self.hl_subterm)
                self.cancel_subterm_mode(update_path = False)
                self.aterm.notation.auto_split_lines(self.pp_width)
                self.down_ids = []
                break
            except Exception as e:
                if isinstance(e, ErrorInLine):
                    show_err(str(e.msg))
                    line_edit.cursor = e.start
                else:
                    if isinstance(e, InconsistentValueError) and self.subterm_mode:
                        fv_values = []
                        bvar_values = [None]*aterm_ori.term.debruijn_height
                        for i,(name,value) in zip(aterm_ori.calc_term.used_bvars, e.inputs):
                            bvar_values[-i] = value
                        for v,val in self.abstract_term_subst.items():
                            if v.arity > 0: continue
                            cterm = self.tenv.calculator.build_calc_term(val, dict())
                            val = cterm.evaluate(bvar_values)
                            fv_values.append((v.name, val))
                        e.inputs = fv_values + e.inputs
                    show_err(str(e))
                    # raise

    def log(self, tag, data):
        print(tag+': '+data, file = self.f)
    def log_term(self):
        self.log("TERM", self.aterm.term.to_str(bound_names = ('x',)))
    def log_seq(self):
        
        self.log("SEQ", str(self.aterm.term))

if __name__ == "__main__":
    import os
    import argparse
    os.environ['TERM'] = 'xterm-256color'

    #tenv = ThibaultEnv()
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

    def make_term_imerps():
        code = """
        compr(X, a :
          if 1192 <= a % 1280 && a % 1280 <= 1271 ;
            1 - loop(a // 4, a, b : c :
                if b % (1 + c) <= 0 ; 0 else b)
          else 1)
        """
        line = "B K C C C L D F D G D C K J K K F C C J H B K B L D H A K I K C G C G K J E B I K M"
        term = tenv.letters_to_seq_program(line.split())
        simp_rewriter = SimpRewriter(tenv)
        term = tenv.env.rewriter.run(term, simp_rewriter, repeat = True).term[1]
        return term        

    def make_term_A13108():
        code = """
        (- 1) ^ X * (prod(0 .. X - 1, z : 1 + (2 * z + 1) ^ 2)
          + 2 * X * prod(0 .. X - 1, z : 1 + (2 * z) ^ 2))
        """
        line = "A K E K B L K L F L F K D C L D K C G B K C H N K L F A L K E B K N F A B B K L H D L N F K D D L K A K N K G B B K K D D J B E J"
        term = tenv.letters_to_seq_program(line.split())
        simp_rewriter = SimpRewriter(tenv)
        term = tenv.env.rewriter.run(term, simp_rewriter, repeat = True).term[1]
        return term

    def make_term_A1136():
        code = """
        comprb(x, c :
          (c % 6 = 1 && c in primes)
          && loop(c // 6 - 1, 2, b : d : (if b = 1 ; 3 else 2 * b) % c) = 1)
        """
        return tenv.env.parser.parse_str(code)

    def take_program_from_stdin():
        import sys
        print("Input a program in the letters format")
        line = sys.stdin.readline()
        term = tenv.letters_to_seq_program(line.split())
        simp_rewriter = SimpRewriter(tenv)
        term = tenv.env.rewriter.run(term, simp_rewriter, repeat = True).term[1]
        return term

    cmd_parser = argparse.ArgumentParser(prog='thibault_tui.py',
                                         description='examinor of generated OEIS programs',
                                         formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    cmd_parser.add_argument("--num_eval", type=int, default = "20", help="Number of points wher the program gets evaluated")
    cmd_parser.add_argument("fname", type=str, help="File with examined program")
    #cmd_parser.add_argument("--test", action = "store_true", default = False, help="Uses prepared program instead of reading from stdin")
    config = cmd_parser.parse_args()
    #if config.test: program = make_term_A1136()
    #else: program = take_program_from_stdin()
    curses.wrapper(ThibaultTui, config.fname, config.num_eval)
