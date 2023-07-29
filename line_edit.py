import curses

KEY_LEFT = "KEY_LEFT"
KEY_RIGHT = "KEY_RIGHT"
KEY_BACKSPACE = "\x08"
KEY_DELETE = "KEY_DC"
KEY_CTRL_LEFT = "kLFT5"
KEY_CTRL_RIGHT = "kRIT5"
KEY_CTRL_BACKSPACE = "KEY_BACKSPACE"
KEY_HOME = "KEY_HOME"
KEY_END = "KEY_END"
KEY_ENTER = "\n"
KEY_TAB = "\t"
KEY_F10 = "KEY_F(10)"

class LineEdit:
    def __init__(self, scr, win_y = -1, win_x = 0, win_width = 0):
        if win_width <= 0 or win_y < 0 or win_x < 0:
            height,width = scr.getmaxyx()
            if win_y < 0: win_y += height
            if win_x < 0: win_x += width
            if win_width <= 0: win_width += width - win_x
        self.scr = scr
        self._data = []
        self._shift = 0
        self._win_y = win_y
        self._win_x = win_x+2
        self._win_width = win_width-4
        self._updated = False
        self._cursor = 0
        self._highlight = None
        self._draw(True)

    @property
    def cursor(self):
        return self._cursor
    @cursor.setter
    def cursor(self, value):
        if value < 0: self._cursor = 0
        elif value > len(self._data): self._cursor = len(self._data)
        else: self._cursor = value
        if self._cursor_updated():
            self._draw(True)
        else:
            self._set_cursor()

    @property
    def data(self):
        return ''.join(self._data)

    def _clear(self):
        self.scr.addstr(self._win_y, self._win_x-2, ' '*(self._win_width+3))
        self.scr.insch(self._win_y, self._win_x + self._win_width+1, ' ')

    def _draw(self, force = False):
        if not (self._updated or force): return
        s = ''.join(self._data[self._shift:self._shift+self._win_width])
        self._clear()
        if self._highlight is not None and 0 <= self._highlight-self._shift < self._win_width:
            hli = self._highlight-self._shift
            self.scr.addstr(self._win_y,self._win_x,s[:hli])
            self.scr.addstr(s[hli], curses.A_UNDERLINE)
            self.scr.addstr(s[hli+1:])
        else:
            self.scr.addstr(self._win_y, self._win_x,s)

        if self._shift > 0:
            self.scr.addch(self._win_y,self._win_x-2,'<')
        else:
            self.scr.addch(self._win_y,self._win_x-2,'>')
        if self._shift < len(self._data) - self._win_width:
            self.scr.insch(self._win_y,self._win_x+self._win_width+1,'>')
        self._set_cursor()
        self._updated = False

    def _set_cursor(self):
        self.scr.move(self._win_y, self._win_x + self._cursor - self._shift)
    def _cursor_updated(self):
        return self._cursor_shift_updated() | self._highlight_updated()
    def _cursor_shift_updated(self):
        if self._shift > self._cursor:
            self._shift = self._cursor
            return True
        elif self._shift <= self._cursor - self._win_width:
            self._shift = self._cursor - self._win_width+1
            return True
        elif self._shift > max(len(self._data) - self._win_width+1, 0):
            self._shift = max(len(self._data) - self._win_width+1, 0)
            return True
        else:
            return False
    def _highlight_updated(self):
        highlight = None
        if self._cursor < len(self._data):
            c = self._data[self._cursor]
            par_in = ('[','(')
            par_out = (']', ')')
            # self.scr.move(0,0)
            # self.scr.addstr(f"c = '{c}'     \n")
            if c in par_in + par_out:
                if c in par_in: shift = 1
                else:
                    par_in,par_out = par_out,par_in
                    shift = -1
                stack = []
                i = self._cursor
                while True:
                    # self.scr.addstr(f"i = {i}, c = '{c}'     \n")
                    if c in par_in:
                        stack.append(par_in.index(c))
                        # self.scr.addstr(f"extended stack: {stack}\n")
                    elif c in par_out:
                        if par_out.index(c) != stack.pop():
                            # self.scr.addstr(f"incompatible parentheses   \n")
                            break
                        if not stack:
                            highlight = i
                            # self.scr.addstr(f"HL set to {i}   \n")
                            break
                        # self.scr.addstr(f"reduced stack: {stack}\n")
                    i += shift
                    if not (0 <= i < len(self._data)):
                        # self.scr.addstr(f"out of data\n")
                        break
                    c = self._data[i]
            # self.scr.addstr("        ")
            # self._set_cursor()
        if highlight != self._highlight:
            self._highlight = highlight
            return True
        else: return False

    def insert(self, s, index = None):
        if index is None: index = self._cursor
        self._updated = True
        s = list(s)
        self._data[index:index] = s
        if self.cursor >= index: self.cursor += len(s)
        self._draw()
    def delete(self, i0, i1):
        if i0 < 0: i0 = 0
        elif i0 >= len(self._data): return
        if i1 > len(self._data): i1 = len(self._data)
        elif i1 <= 0: return
        if i0 >= i1: return
        self._updated = True
        del self._data[i0:i1]
        if self.cursor >= i0:
            self.cursor = max(i0, self.cursor - (i1-i0))
        else:
            self._cursor_shift_updated()
        self._draw()

    def jump_left(self, i = None):
        if i is None: i = self._cursor
        if i > len(self._data): i = len(self._data)
        i -= 1
        while i >= 0 and not self._data[i].isalnum(): i -= 1
        while i >= 0 and self._data[i].isalnum(): i -= 1
        return i+1
    def jump_right(self, i = None):
        if i is None: i = self._cursor
        if i < 0: i = 0
        n = len(self._data)
        while i < n and not self._data[i].isalnum(): i += 1
        while i < n and self._data[i].isalnum(): i += 1
        return i

    def loop(self):
        while True:
            self.scr.refresh()
            c = self.scr.getkey()
            if c == KEY_RIGHT: self.cursor += 1
            elif c == KEY_LEFT: self.cursor -= 1
            elif c == KEY_BACKSPACE: self.delete(self.cursor-1, self.cursor)
            elif c == KEY_DELETE: self.delete(self.cursor, self.cursor+1)
            elif c == KEY_CTRL_LEFT: self.cursor = self.jump_left()
            elif c == KEY_CTRL_RIGHT: self.cursor = self.jump_right()
            elif c == KEY_CTRL_BACKSPACE: self.delete(self.jump_left(), self.cursor)
            elif c == KEY_HOME: self.cursor = 0
            elif c == KEY_END: self.cursor = len(self._data)
            elif c == KEY_TAB:
                if self._highlight is not None: self.cursor = self._highlight
            elif c == KEY_ENTER: return self.data
            elif c == KEY_F10: return None # escape
            elif len(c) == 1 and c.isprintable(): self.insert(c)

if __name__ == "__main__":
    def main(scr):
        global res
        line_edit = LineEdit(scr)

        res = line_edit.loop()

    curses.wrapper(main)
    if res is None: print("No output")
    else: print("Output:", res)
