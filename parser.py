from lexer import Token, Lexer

class SyntaxTree:
    def __init__(self, rule, args):
        self.rule = rule
        self.args = args
        self.parent = None
        for i,arg in enumerate(args):
            arg.parent = self,i

    def to_lines(self):
        offset = 0
        cols = []
        for arg in self.args:
            if isinstance(arg, SyntaxTree):
                lines = arg.to_lines()
                lines = [' '*len(lines[0])]+lines
                cols.append(lines)
            elif isinstance(arg, Token):
                cols.append([arg.name])
            else: raise Exception()

        # align
        depth = max(len(col) for col in cols)
        for col in cols:
            if len(col) < depth:
                col += [' '*len(col[0])]*(depth-len(col))

        return [
            ' '.join(row)
            for row in zip(*cols)
        ]

    def print_self(self):
        for line in self.to_lines():
            print(line)

class SyntaxRule:
    def can_pack(self, objects):
        raise Exception("Not implemented")
    def should_pack(self, objects, next_token):
        return self.can_pack(objects)
    def can_take_token(self, objects, token):
        raise Exception("Not implemented")
    def can_take_object(self, objects):
        raise Exception("Not implemented")
    def get_literals(self):
        return []

    def compatible_inner(self, other):
        return True

    def try_inside(self, objects, token):
        if not hasattr(self, "parser"): return None

        if objects and isinstance(objects[-1], SyntaxTree):
            rule1 = self.parser.get_rule1(token)
            if rule1 is None: return None
            if self.can_take_token(objects, token): return None
            #if (not self.should_pack(objects, token)) or
            if (not self.can_pack(objects) or self.compatible_inner(rule1)):
                return rule1
        elif self.can_take_object(objects):
            rule0 = self.parser.get_rule0(token)
            if rule0 == None: return None
            return rule0

class PrecedenceGroup:
    def __init__(self, inside = (), outside = (), assoc_left = False, assoc_right = False, tight = True):
        lower = inside
        higher = outside
        assert not (assoc_left and assoc_right)
        if isinstance(lower, PrecedenceGroup): lower = [lower]
        if isinstance(higher, PrecedenceGroup): higher = [higher]
        lower_all = set(lower)
        higher_all = set(higher)
        if lower and higher:
            assert all(
                h in l.higher
                for l in lower
                for h in higher
            )
        if not lower:
            if tight and higher:
                lower_all = set(higher[0].lower)
                for h in higher[1:]:
                    lower_all.intersection_update(h.lower)
        else:
            for x in lower:
                lower_all.update(x.lower)

        if not higher:
            if tight and lower:
                higher_all = set(lower[0].higher)
                for h in lower[1:]:
                    higher_all.intersection_update(h.higher)
        else:
            for x in higher:
                higher_all.update(x.higher)

        self.lower = lower_all
        self.higher = higher_all
        for x in lower_all:
            x.higher.add(self)
        for x in higher_all:
            x.lower.add(self)
        self.assoc_left = assoc_left
        self.assoc_right = assoc_right
    def is_higher_than(self, other):
        return other in self.lower
    def is_lower_than(self, other):
        return other in self.higher

class SyntaxWithPrecedence(SyntaxRule):
    def __init__(self, precedence = None, **precedence_kwargs):
        super().__init__()
        if precedence is None:
            precedence = PrecedenceGroup(**precedence_kwargs)
        else:
            assert not precedence_kwargs
        self.precedence = precedence

    def should_pack(self, objects, next_token):
        if not self.can_pack(objects): return False
        if isinstance(objects[-1], Token): return True
        rule1 = self.parser.get_rule1(next_token)
        if rule1 is None: return True
        return self.compatible_outer(rule1)

    def compatible_inner(self, other):
        if not isinstance(other, SyntaxWithPrecedence): return False
        precedence1 = self.precedence
        precedence2 = other.precedence
        if precedence1 == precedence2:
            return precedence1.assoc_right
        return precedence2.is_higher_than(precedence1)
    def compatible_outer(self, other):
        if not isinstance(other, SyntaxWithPrecedence): return False
        precedence1 = self.precedence
        precedence2 = other.precedence
        if precedence1 == precedence2:
            return precedence1.assoc_left
        return precedence1.is_higher_than(precedence2)
        return False

class SyntaxBasic(SyntaxWithPrecedence):
    def __init__(self, *elements, accepts_modified = False, **precedence_kwargs):
        super().__init__(**precedence_kwargs)
        self.elements = elements
        self.accepts_modified = accepts_modified

    def can_pack(self, objects):
        return len(objects) == len(self.elements)
    def can_take_token(self, objects, token):
        index = len(objects)
        if token.t == "NEG":
            if not self.accepts_modified: return False
            if any(isinstance(x, Token) for x in objects): return False
        elif token.t != "LIT": return False
        return index < len(self.elements) and self.elements[index] == token.name
    def can_take_object(self, objects):
        index = len(objects)
        return index < len(self.elements) and not isinstance(self.elements[index], str)
    def get_literals(self):
        for i,x in enumerate(self.elements):
            if isinstance(x, str):
                yield i,x

    def objects_to_str(self, objects, rule_left = None, rule_right = None, **kwargs):
        objects_it = iter(objects)
        res = []
        bracketed = False
        if isinstance(self.elements[0], str): rule_left = None
        if isinstance(self.elements[-1], str): rule_right = None

        if rule_left is not None:
            if not rule_left.compatible_inner(self):
                bracketed = True
        if rule_right is not None:
            if self.compatible_inner(rule_right):
                bracketed = True
            if not self.compatible_outer(rule_right):
                bracketed = True

        if bracketed:
            rule_left = None
            rule_right = None
        for i,elem in enumerate(self.elements):
            if elem is None:
                obj = next(objects_it)
                cur_rule_left = None
                cur_rule_right = None
                if i == 0:
                    cur_rule_left = rule_left
                    cur_rule_right = self
                elif i == len(self.elements)-1:
                    cur_rule_left = self
                    cur_rule_right = rule_right
                res.append(obj.to_str(
                    rule_left = cur_rule_left,
                    rule_right = cur_rule_right,
                    **kwargs,
                ))
            else: res.append(elem)

        res = ' '.join(res)
        if bracketed: res = '('+res+')'
        return res

class SyntaxBasicOuter(SyntaxBasic):
    def should_pack(self, objects, next_token):
        return False
    def compatible_inner(self, other):
        return True

class SyntaxAtom(SyntaxRule):
    def can_pack(self, objects):
        return len(objects) == 1
    def can_take_token(self, objects, token):
        return not objects and token.t != "LIT"
    def can_take_object(self, objects):
        return False

class SyntaxMain(SyntaxRule):
    def __init__(self, parser):
        self.parser = parser
    def should_pack(self, objects, next_token):
        return False
    def can_pack(self, objects):
        return len(objects) == 1
    def can_take_token(self, objects, token):
        return False
    def can_take_object(self, objects):
        return not objects

class SyntaxFunApp(SyntaxWithPrecedence):
    def can_pack(self, objects):
        return isinstance(objects[-1], Token) and objects[-1].name == ')'
    def can_take_token(self, objects, token):
        if token.t != 'LIT': return False
        i = len(objects)
        if i%2 == 0: return False
        if i == 1: return token.name == '('
        else: return token.name in (',', ')')
    def can_take_object(self, objects):
        if len(objects) % 2 == 1: return False
        if objects and objects[-1].name == ')': return False
        return True
    def get_literals(self):
        return [
            (1,'('),
            (3,','),
            (3,')'),
        ]

class Parser:
    def __init__(self, lexer = None):
        if lexer is None: self.lexer = Lexer()
        else: self.lexer = lexer
        self._literal_to_rule0 = dict()
        self._literal_to_rule1 = dict()
        self._operator_modifiers = dict()
        self._rule_atom = SyntaxAtom()
        self._rule_main = SyntaxMain(self)
    def set_line_comment(self, lit):
        self.lexer.set_line_comment(lit)
    def add_operator_modifier(self, literal, term_type1, term_type2):
        self._operator_modifiers[literal] = (term_type1, term_type2)
    def add_rule(self, rule, allow_inside = True):
        rule.parser = self
        for i,lit in rule.get_literals():
            self.lexer.add_literal(lit)
            d = None
            if i == 0: d = self._literal_to_rule0
            elif i == 1: d = self._literal_to_rule1
            if d is not None and allow_inside:
                if lit in d:
                    raise Exception(f"Multiple rules for a single key: {(lit,i)}")
                d[lit] = rule
        return rule
    def get_rule0(self, token):
        if token.t in ("LIT", "NEG"):
            return self._literal_to_rule0.get(token.name, None)
        else:
            return self._rule_atom
    def get_rule1(self, token):
        if token.t in ("LIT", "NEG"):
            return self._literal_to_rule1.get(token.name, None)
        else:
            return None

    def precedence_of(self, literal, i = 1, try_both = True):
        if i == 0: d = self._literal_to_rule0
        elif i == 1: d = self._literal_to_rule1
        else: raise Exception(f"Unexpected key index: {i}")
        rule = d.get(literal, None)
        if rule is None:
            if try_both: return self.precedence_of(literal, 1-i, False)
            else: raise Exception("Referred rule not found")
        return rule.precedence

    def ini_state(self, rule = None):
        if rule is None: rule = self._rule_main
        return ParserState(rule)

class ParserState:
    def __init__(self, main_rule):
        self.parser = main_rule.parser
        self.stack = [(main_rule, [])]
        self.active_modifier = None

    def add_token(self, token):
        if self.active_modifier is not None:
            t1,t2 = self.active_modifier
            assert token.t == t1
            token.t = t2
            self.active_modifier = None
        rule, objects = self.stack[-1]
        while True:
            next_rule = rule.try_inside(objects, token)
            if False and isinstance(rule, SyntaxBasic) and isinstance(next_rule, SyntaxBasic):
                print(rule.elements, next_rule.elements)
                print(rule.compatible_inner(next_rule))
                print(rule.should_pack(objects))
            if next_rule is not None:
                next_objects = []
                if next_rule.can_take_object(next_objects):
                    next_objects.append(objects.pop())
                if not next_rule.can_take_token(next_objects, token):
                    token.show_in_line()
                    print(next_rule.elements)
                    print(next_rule.accepts_modified)
                    raise Exception
                next_objects.append(token)
                self.stack.append((next_rule, next_objects))
                break
            if token.t == "LIT" and token.name in self.parser._operator_modifiers:
                self.active_modifier = self.parser._operator_modifiers[token.name]
                break

            if rule.can_take_token(objects, token):
                objects.append(token)
                break

            if not self.stack:
                token.show_in_line()
                raise Exception()
            if not rule.should_pack(objects, token):
                token.show_in_line()
                raise Exception()
            obj = SyntaxTree(rule, objects)
            self.stack.pop()
            rule, objects = self.stack[-1]
            assert rule.can_take_object(objects), (objects, type(rule))
            objects.append(obj)

    def parse_line(self, line, lineno = None):
        for token in self.parser.lexer.parse_line(line, lineno = lineno):
            self.add_token(token)

    def finish(self):
        rule, objects = self.stack.pop()
        assert rule.can_pack(objects)
        res = SyntaxTree(rule, objects)
        while self.stack:
            rule, objects = self.stack.pop()
            objects.append(res)
            assert rule.can_pack(objects)
            res = SyntaxTree(rule, objects)
        return res

if __name__ == "__main__":
    lexer = Lexer()
    parser = Parser(lexer)
    parser.add_rule(SyntaxFunApp())
    parser.add_rule(SyntaxBasic('(', None, ')'))
    parser.add_rule(SyntaxBasic(
        None, ':', None,
        assoc_right = True,
        outside = parser.precedence_of('(')
    ))

    line = "f(A,x:y:B(x,y),C)"

    parser_state = parser.ini_state()
    parser_state.parse_line(line)
    res = parser_state.finish()
    res.print_self()
