import re

def show_in_line(line, start, end = None, lineno = None):
    if end is None: l = 1
    else: l = end-start
    if lineno is not None:
        line_desc = "{}:".format(lineno)
        start += len(line_desc)
        line = line_desc+line
    print(line)
    print(' '*start+'^'*l)

class Token:
    def __init__(self, name, t):
        self.name = name
        self.t = t
    def show_in_line(self):
        show_in_line(self.line, self.start, self.end, self.lineno)

class Lexer:
    def __init__(self):
        self.literals = set()
        self.prefixes = set()
        self.regex = [
            ('NUM', re.compile("[0-9]+")),
            ('VAR', re.compile("[a-zA-Z_][_a-zA-Z0-9]*")),
        ]
        self.word_literals = set()

    def add_literal(self, lit):
        for i in range(1, len(lit)):
            self.prefixes.add(lit[:i])
        self.literals.add(lit)

    def parse_line(self, line, lineno = None, fname = None):
        i = 0
        while i < len(line):
            if line[i].isspace():
                i += 1
                continue
            # search for a token
            j = i+1
            token_end = None
            while j <= len(line):
                s = line[i:j]
                if s in self.literals:
                    token_end = j
                    token_type = "LIT"
                if s not in self.prefixes: break
                j += 1

            for regex_type, regex in self.regex:
                match = regex.match(line,i)
                if match is None: continue
                if token_end is None or token_end < match.end():
                    token_end = match.end()
                    token_type = regex_type

            if token_end is None:
                if fname is not None: print("File:", fname)
                show_in_line(line, i, lineno = lineno)
                raise Exception("Lexer: Unknown token")

            token = Token(line[i:token_end], token_type)
            token.lineno = lineno
            token.fname = fname
            token.line = line
            token.start = i
            token.end = token_end
            i = token_end

            yield token

if __name__ == "__main__":
    lexer = Lexer()
    lexer.add_literal('=>')
    lexer.add_literal('-')
    lexer.add_literal('exists')
    lexer.add_literal('exists!')

    for token in lexer.parse_line("X existsuje exists! - 14 => 13b - a13", lineno = 123):
        token.show_in_line()
