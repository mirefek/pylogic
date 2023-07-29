import re

class Token:
    def __init__(self, name, t):
        self.name = name
        self.t = t

class ErrorInLine(Exception):
    def __init__(self, exc, line_or_token, start = None, end = None, lineno = None):
        self.exc = exc
        if isinstance(line_or_token, Token):
            token = line_or_token
            self.line = token.line
            self.start = token.start
            self.l = token.end - token.start
            self.lineno = token.lineno
        else:
            self.line = line_or_token
            self.start = start
            if end is None: self.l = 1
            else: self.l = end - start
            self.lineno = lineno

    def line_str(self):
        start = self.start
        line = self.line
        if self.lineno is not None:
            line_desc = "{}:".format(self.lineno)
            start += len(line_desc)
            line = line_desc+line
        if line.endswith('\n'): line = line[:-1]
        return line+'\n'+' '*start+'^'*self.l

    def __str__(self):
        return str(self.exc) + '\n' + self.line_str()
    
class Lexer:
    def __init__(self):
        self.literals = set()
        self.prefixes = set()
        self.regex = [
            ('NUM', re.compile("[0-9]+")),
            ('VAR', re.compile("[a-zA-Z_][_a-zA-Z0-9]*")),
        ]
        self.word_literals = set()
        self.line_comments = set()

    def add_literal(self, lit):
        for i in range(1, len(lit)):
            self.prefixes.add(lit[:i])
        self.literals.add(lit)

    def set_line_comment(self, lit):
        self.add_literal(lit)
        self.line_comments.add(lit)

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
                raise ErrorInLine("Lexer: Unknown token", line, i, lineno = lineno)

            token = Token(line[i:token_end], token_type)
            if token.name in self.line_comments: return
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
    lexer.set_line_comment('#')
