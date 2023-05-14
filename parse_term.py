from term import *
from parser import *
from logic_core import LogicCore

class TermParser:
    def __init__(self, logic, int_to_term = None):
        self.logic = logic
        self.name_arity_to_var = dict()
        self.name_signature_to_const = dict()
        self.const_to_age = dict()
        self.consts_by_age = []
        self.name_to_axiom = dict()
        self.syntax_parser = Parser()
        self.syntax_parser.set_line_comment('#')
        self.last_line = 0,''
        self.cur_fname = None
        self.int_to_term = int_to_term
        self.verbose = False

        parenth = self.add_syntax_rule(SyntaxBasic(
            '(', None, ')',
        ))
        parenth.semantics = lambda dummy1,arg,dummy2: self.tree_to_term(arg)
        self.add_syntax_rule(SyntaxFunApp()).semantics = self._funapp
        self.syntax_parser._rule_atom.semantics = self._nulary_const_or_var
        self.syntax_colon = self.add_syntax_rule(SyntaxBasic(
            None, ':', None,
            assoc_right = True,
            outside = self.syntax_parser.precedence_of('(')
        ))
        self.def_syntax = self.add_syntax_rule(SyntaxBasicOuter(
            None, ':=', None
        ), allow_inside = False)
        self.ax_syntax = self.add_syntax_rule(SyntaxBasicOuter(
            None, ':', None
        ), allow_inside = False)
        self.eq_precedence = None
        self.neg_function = None

    def add_syntax_rule(self, rule, **kwargs):
        return self.syntax_parser.add_rule(rule, **kwargs)
    def syntax_state(self):
        return self.parser_to_tree.ini_state()
    def syntax_tree_to_term(self, syntax_tree, introduce_constant = False, with_binders = False):
        self.depth = 0
        self.local_context = dict()
        self.introduce_constant = introduce_constant
        self.new_constant = None
        if with_binders: bound_names, res = self._binder_tree_to_term(syntax_tree)
        else: res = self.tree_to_term(syntax_tree)
        del self.depth
        del self.local_context
        del self.introduce_constant
        new_constant = self.new_constant
        del self.new_constant
        if introduce_constant:
            if with_binders:
                return bound_names, res, new_constant
            else:
                return res, new_constant
        else:
            if with_binders:
                return bound_names, res
            else:
                return res

    def tree_to_term(self, syntax_tree):
        return syntax_tree.rule.semantics(*syntax_tree.args)
    def _nulary_const_or_var(self, token):
        if token.name.isdigit():
            if self.int_to_term is None:
                raise Exception("Numbers not supported, missing conversion to term")
            else:
                return self.int_to_term(int(token.name))
        bvi = self.local_context.get(token.name, None)
        if bvi is not None:
            return BVar(self.depth - bvi)
        else:
            x = self._get_const_or_var(token.name, ())
            assert x is not None
            return TermApp(x, ())
    def _get_string(self, tree):
        if tree.rule != self.syntax_parser._rule_atom: return None
        return tree.args[0].name

    def _binder_tree_to_term(self, tree):
        bvs = []
        while tree.rule == self.syntax_colon:
            bv = self._get_string(tree.args[0])
            assert bv is not None
            bvs.append(bv)
            tree = tree.args[2]
        if bvs:
            local_context_ori = dict(self.local_context)
            for bv in bvs:
                assert not bv.isdigit()
                self.local_context[bv] = self.depth
                self.depth += 1
        term = self.tree_to_term(tree)
        if bvs:
            self.depth -= len(bvs)
            self.local_context = local_context_ori
        return tuple(bvs), term

    def _funapp(self, *args):
        fun = self._get_string(args[0])
        assert fun != None
        assert not fun.isdigit()
        assert fun not in self.local_context
        introduce_constant = self.introduce_constant
        self.introduce_constant = False
        term_args = [
            self._binder_tree_to_term(arg)
            for arg in args[2::2]
        ]
        bound_names = tuple(bn for bn,_ in term_args)
        term_args = tuple(term_arg for _,term_arg in term_args)
        signature = tuple(len(bn) for bn in bound_names)
        self.introduce_constant = introduce_constant
        f = self._get_const_or_var(fun, signature)
        self.introduce_constant = False
        res = TermApp(f, term_args, bound_names = bound_names)
        return res

    def get_var(self, name, arity):
        v = self.name_arity_to_var.get((name, arity), None)
        if v is not None: return v
        v = TermVariable(arity, name = name)
        self.name_arity_to_var[name, arity] = v
        return v

    def _get_const_or_var(self, name, signature):
        if self.introduce_constant and self.new_constant is None:
            for core_constant in (self.logic.implication, self.logic.equality):
                if name == core_constant.name:
                    assert signature == core_constant.signature
                    const = core_constant
                    break
            if name == self.logic.implication.name:
                assert signature == (0,0)
                const = self.logic.implication
            elif name == "__eq__":
                assert signature == (0,0)
                const = self.logic.equality
            else: const = TermConstant(signature, name = name)
            self.new_constant = const
            return const
        const = self.name_signature_to_const.get((name, signature), None)
        if const is not None: return const

        assert all(x == 0 for x in signature), (name, signature)
        return self.get_var(name, len(signature))

    def parse_file(self, fname, verbose = False):
        verbose_ori=  self.verbose
        self.verbose = verbose
        self.cur_fname = fname
        with open(fname) as f:
            self.parse_lines(f)
        self.cur_fname = None
        self.verbose = verbose_ori

    def parse_lines(self, lines):
        state = ParseTermState(self)
        for i,line in enumerate(lines):
            state.add_line(line, i+1)
        self.last_line = 0,''
        state.finish()

    def parse_str(self, s, **kwargs):
        syntax_state = self.syntax_parser.ini_state()
        if '\n' in s:
            for i,line in enumerate(s.split('\n')):
                syntax_state.parse_line(line,i)
        else:
            syntax_state.parse_line(s,0)
        syntax_tree = syntax_state.finish()
        [syntax_tree] = syntax_tree.args
        return self.syntax_tree_to_term(syntax_tree, **kwargs)

    def get_header_var_list_(self, term, f):
        assert term.f == f
        res = []
        res_s = set()
        for arg in term.args:
            v = arg.f
            assert isinstance(v, TermVariable)
            assert v not in res_s
            for i, v_arg in enumerate(arg.args):
                assert isinstance(v_arg, BVar)
                assert v_arg.debruijn_height == v.arity-i
            res_s.add(v)
            res.append(v)
        return res

    def register_constant(self, c):
        assert (c.name, c.signature) not in self.name_signature_to_const
        self.name_signature_to_const[c.name, c.signature] = c
        age = len(self.consts_by_age)
        self.consts_by_age.append(c)
        self.const_to_age[c] = age
    def add_constant(self, syntax_tree):
        t,c = self.syntax_tree_to_term(syntax_tree, True)
        self.get_header_var_list_(t,c)
        self.register_constant(c)
    def add_definition(self, header, _, body):
        header,c = self.syntax_tree_to_term(header, True)
        var_list = self.get_header_var_list_(header,c)
        body = self.syntax_tree_to_term(body)
        assert (c.name, c.signature) not in self.name_signature_to_const
        c = self.logic.add_definition(
            var_list, body,
            name = c.name,
            bound_names = header.bound_names
        )
        self.register_constant(c)
        if self.verbose:
            print("Definition:", c.def_core_thm.term)
    def add_axiom(self, name, _, body):
        assert name.rule == self.syntax_parser._rule_atom
        name = name.args[0].name
        body = self.syntax_tree_to_term(body)
        axiom = self.logic.add_axiom(body, [self.cur_fname, self.last_line[0]])
        self.name_to_axiom[name] = axiom
        if self.verbose:
            print("Axiom:", axiom)

    def check_eq_rule(self, f_name, rule):
        if self.eq_precedence is None and f_name == "__eq__":
            self.eq_precedence = rule.precedence
    def check_accepts_modified(self, f_name, rule):
        if self.eq_precedence is None: return
        if (
                rule.precedence != self.eq_precedence and
                not rule.precedence.is_lower_than(self.eq_precedence)
        ): return
        if len(rule.elements) < 2: return
        if isinstance(rule.elements[0], str): return
        if not isinstance(rule.elements[1], str): return
        rule.accepts_modified = True
    def check_neg_rule(self, f_name, rule):
        if self.neg_function is not None: return
        if len(rule.elements) != 2: return
        if f_name != "_neg": return
        if not isinstance(rule.elements[0], str): return
        if isinstance(rule.elements[1], str): return
        self.neg_function = self.name_signature_to_const[f_name, (0,)]
        self.syntax_parser.add_operator_modifier(rule.elements[0], "LIT", "NEG")

class ParseTermState:
    def __init__(self, parser):
        self.parser = parser
        self.syntax_parser = parser.syntax_parser
        self.syntax_state = None
        self.syntax_purpose = None
        self.parser.last_line = 0,''

    def add_line(self, line, lineno):
        if not line.strip(): return
        line_start = None
        if line and not line[0].isspace():
            line_start = line.split(' ', 1)[0]
        if line_start == "Constant":
            self.finish()
            self.parser.last_line = lineno, line
            self.syntax_state = self.syntax_parser.ini_state()
            self.syntax_purpose = self.parser.add_constant
            self.syntax_state.parse_line(line.split(' ', 1)[1], lineno)
        elif line_start == "Definition":
            self.finish()
            self.parser.last_line = lineno, line
            self.syntax_state = self.syntax_parser.ini_state(self.parser.def_syntax)
            self.syntax_purpose = self.parser.add_definition
            self.syntax_state.parse_line(line.split(' ', 1)[1], lineno)
        elif line_start == "Axiom":
            self.finish()
            self.parser.last_line = lineno, line
            self.syntax_state = self.syntax_parser.ini_state(self.parser.ax_syntax)
            self.syntax_purpose = self.parser.add_axiom
            self.syntax_state.parse_line(line.split(' ', 1)[1], lineno)

        elif line_start == "Notation":
            self.finish()
            self.parser.last_line = lineno, line
            # Basic line parsing
            all_tokens = line.split()
            f = all_tokens[1]
            i = 2
            j = i
            line_parts = []
            for j in range(i,len(all_tokens)):
                if len(all_tokens[j]) > 2 and all_tokens[j].isupper():
                    line_parts.append(all_tokens[i:j])
                    i = j
            line_parts.append(all_tokens[i:])
            syntax_elements = [
                (x if x != '_' else None)
                for x in line_parts[0]
            ]

            # getting precedence arguments
            inside = []
            outside = []
            precedence = None
            assoc_left = False
            assoc_right = False
            for cmd,*args in line_parts[1:]:
                if cmd == "INSIDE":
                    inside.extend(
                        self.syntax_parser.precedence_of(x)
                        for x in args
                    )
                elif cmd == "OUTSIDE":
                    outside.extend(
                        self.syntax_parser.precedence_of(x)
                        for x in args
                    )
                elif cmd == "PRECEDENCE":
                    assert precedence is None
                    [arg] = args
                    precedence = self.syntax_parser.precedence_of(arg)
                elif cmd == "ASSOCLEFT":
                    assert not args
                    assoc_left = True
                elif cmd == "ASSOCRIGHT":
                    assert not args
                    assoc_right = True

            if precedence is None:
                if syntax_elements[0] is None or syntax_elements[-1] is None:
                    assert inside or outside, line
                precedence_kwargs = {
                    "inside": inside,
                    "outside": outside,
                    "assoc_left": assoc_left,
                    "assoc_right": assoc_right,
                }
            else:
                assert not inside
                assert not outside
                assert not assoc_left
                assert not assoc_right
                precedence_kwargs = {
                    "precedence": precedence,
                }
            syntax_rule = self.parser.add_syntax_rule(SyntaxBasic(
                *syntax_elements,
                **precedence_kwargs,
            ))

            # check special rules

            self.parser.check_eq_rule(f, syntax_rule)
            self.parser.check_accepts_modified(f, syntax_rule)
            self.parser.check_neg_rule(f, syntax_rule)

            # semantics
            arg_is = [
                i
                for i,x in enumerate(syntax_elements)
                if x is None
            ]
            f = self.parser.name_signature_to_const[f, (0,)*len(arg_is)]
            if syntax_rule.accepts_modified:
                def semantics(*args):
                    res = TermApp(f, tuple(
                        self.parser.tree_to_term(args[i]) for i in arg_is
                    ))
                    if args[1].t == "NEG":
                        res = TermApp(self.parser.neg_function, (res,))
                    return res
            else:
                def semantics(*args):
                    return TermApp(f, tuple(
                        self.parser.tree_to_term(args[i]) for i in arg_is
                    ))

            f.notation = syntax_rule
            syntax_rule.semantics = semantics

        elif self.syntax_state is not None:
            self.parser.last_line = lineno, line
            self.syntax_state.parse_line(line, lineno)
        elif any(True for token in self.syntax_parser.lexer.parse_line(line)):
            print(f"{lineno}:{line.strip()}")
            raise Exception("Nonempty line without context")

    def finish(self):
        if self.syntax_state is None: return
        try:
            syntax_tree = self.syntax_state.finish()
            self.syntax_purpose(*syntax_tree.args)
        except Exception:
            lineno, line = self.parser.last_line
            print(str(lineno)+":"+line)
            raise
        self.syntax_state = None
        self.syntax_purpose = None

if __name__ == "__main__":
    logic = LogicCore()
    parser = TermParser(logic)
    parser.parse_file("axioms_logic", verbose = True)
    parser.parse_file("axioms_set", verbose = True)
    parser.parse_file("axioms_fun", verbose = True)
    #print(parser.parse_str("A = B = C"))
