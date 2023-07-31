from term import Term, TermApp, BVar, get_unused_name
from calculator import Calculator, CalcTerm

class ATNotation:
    def __init__(self, aterm):
        self.aterm = aterm
        self.parts = []
        self.spaces = []
        self.arg_i_to_part_i = []

        if isinstance(self.term, BVar):
            self.parts.append(ATNBvar(self.aterm, self.term.debruijn_height))
            return

        if self.term.f.notation is not None:
            self.build_operator_syntax()
        else: self.build_function_syntax()

    @property
    def term(self):
        return self.aterm.term

    def build_function_syntax(self):
        self.parts.append(self.term.f.name)
        if self.term.f.arity == 0: return
        self.spaces.append('')
        self.parts.append('(')
        self.spaces.append('')
        for subaterm in self.aterm.subterms:
            if self.arg_i_to_part_i:
                self.parts.append(',')
                self.spaces.append(' ')
            self._add_subterm(subaterm)
            self.spaces.append('')
        self.parts.append(')')

    def build_operator_syntax(self):
        bracketed = self.check_bracket_necesity()
        if bracketed:
            self.parts.append('(')
            self.spaces.append('')

        rule = self.term.f.notation
        first_elem = True
        for elem in rule.elements:
            if not first_elem: self.spaces.append(' ')
            else: first_elem = False
            if elem is None:
                arg_i = len(self.arg_i_to_part_i)
                part_i = len(self.parts)
                self._add_subterm(self.aterm.subterms[arg_i])
            else: self.parts.append(elem)

        if bracketed:
            self.spaces.append('')
            self.parts.append(')')

    def _add_subterm(self, subaterm):
        n = len(subaterm.new_bound_names)

        for i in range(n):
            self.parts.append(ATNBinder(self.aterm, subaterm.parent_i, i))
            self.spaces.append(' ')
            self.parts.append(':')
            self.spaces.append(' ')

        self.arg_i_to_part_i.append(len(self.parts))
        self.parts.append(ATNSubterm(self.aterm, subaterm.parent_i))

    def check_bracket_necesity(self):
        rule = self.term.f.notation
        if self.aterm.parent is None: return False
        parent = self.aterm.parent.notation
        parent_rule = parent.term.f.notation
        if parent_rule is None: return False
        parent_i = parent.arg_i_to_part_i[self.aterm.parent_i]

        if parent_i == len(parent.parts)-1: # parent_rule left
            if isinstance(rule.elements[0], str): return False
            if not parent_rule.compatible_inner(rule): return True

        elif parent_i == 0: # parent_rule right
            if isinstance(rule.elements[-1], str): return False
            if rule.compatible_inner(parent_rule): return True
            if not rule.compatible_outer(parent_rule): return True

        return False

    def calculate_str(self):
        n = len(self.parts)
        assert len(self.spaces) == n-1, (self.parts, self.spaces)
        substrs = [None]*(len(self.parts)*2-1)
        substrs[::2] = [str(part) for part in self.parts]
        substrs[1::2] = self.spaces
        self.str_cache = ''.join(substrs)

    def auto_split_lines(self, line_width = 60, indent = 0):
        if indent+len(self.str_cache) < line_width: return
        num_bound = len(self.aterm.new_bound_names)
        next_indent = indent+2
        for subterm in self.aterm.subterms:
            subterm.notation.auto_split_lines(line_width = line_width, indent = next_indent)

        breakable = [True]*len(self.spaces)
        # forbid breaking
        for i,part in enumerate(self.parts):
            if not isinstance(part, str): continue
            if part in (',', ';', ':', ')'): # before selected interpunction
                if i > 0: breakable[i-1] = False
            else: # otherwise after
                if i < len(breakable): breakable[i] = False

        parts = [str(part) for part in self.parts]
        breakable_parts = [[parts[0]]]
        breakable_spaces = []
        space_ids = []
        for i in range(len(breakable)):
            if breakable[i]:
                space_ids.append(i)
                breakable_spaces.append(self.spaces[i])
                breakable_parts.append([parts[i+1]])
            else:
                breakable_parts[-1].extend([self.spaces[i], parts[i+1]])
        breakable_parts = [''.join(part) for part in breakable_parts]

        n = indent + len(breakable_parts[0])
        for before, after, space, idx in zip(breakable_parts[:-1], breakable_parts[1:], breakable_spaces, space_ids):
            if '\n' in after: after_size = after.index('\n')
            else: after_size = len(after)
            after_size += len(space)
            if '\n' in before or n + after_size > line_width:
                if isinstance(self.parts[idx+1], ATNSubterm): n = next_indent
                else: n = indent
                self.spaces[idx] = '\n'+' '*n
            n += after_size
        self.calculate_str()

class ATNPart:
    pass
class ATNBvar(ATNPart):
    def __init__(self, aterm, index):
        self.aterm = aterm
        self.index = index
    def __str__(self):
        return self.aterm.bound_names[-self.index]
class ATNBinder(ATNPart):
    def __init__(self, aterm, ai,vi):
        self.aterm = aterm
        self.ai = ai
        self.vi = vi
    def __str__(self):
        return self.aterm.subterms[self.ai].new_bound_names[self.vi]
class ATNSubterm(ATNPart):
    def __init__(self, aterm, ai):
        self.aterm = aterm
        self.ai = ai
    def __str__(self):
        return self.aterm.subterms[self.ai].notation.str_cache

class FakeCache: # to avoid any sharing in calculation tree
    def get(self, key): return None
    def __setitem__(self, key, value): pass

class AnnotatedTerm:
    def __init__(self, term, parent = None, bound_names = None):
        self.term = term
        if parent is None:
            self.parent, self.parent_i = None, None
            self.new_bound_names = []
            self.taken_names = set(fv.name for fv in term.free_vars)
            if bound_names is None: self.bound_names = []
            else:
                self.bound_names = list(bound_names)
                self.taken_names.update(bound_names)
                assert len(self.taken_names) == len(term.free_vars) + len(bound_names)
            assert len(self.bound_names) >= term.debruijn_height
        else:
            self.parent, self.parent_i = parent
            self.new_bound_names = []
            self.taken_names = set(self.parent.taken_names)
            for name in self.parent.term.bound_names[self.parent_i]:
                name = get_unused_name(name, self.taken_names)
                self.taken_names.add(name)
                self.new_bound_names.append(name)
            self.bound_names = self.parent.bound_names + self.new_bound_names

        if isinstance(self.term, TermApp):
            self.subterms = [
                AnnotatedTerm(arg, (self,i))
                for i,arg in enumerate(term.args)
            ]
        else:
            self.subterms = []

    def replace_subterm(self, i, subterm):
        self.subterms[i] = subterm
        if hasattr(self, 'calc_term'):
            self.calc_term.args[i] = subterm.calc_term
        subterm.parent = self
        subterm.parent_i = i

        aterm = self
        while aterm is not None:
            args = tuple(x.term for x in aterm.subterms)
            aterm.term = TermApp(aterm.term.f, args, aterm.term.bound_names)
            aterm = aterm.parent
        
    def path_to_root(self):
        x = self.parent
        while x is not None:
            yield x
            x = x.parent

    def add_notation(self):
        self.notation = ATNotation(self)
        for subterm in self.subterms:
            subterm.add_notation()
        self.notation.calculate_str()

    def family_from_top(self):
        yield self
        for subterm in self.subterms: yield from subterm.get_family()
    def family_from_bottom(self):
        for subterm in self.subterms: yield from subterm.get_family()
        yield self

    def __str__(self):
        return self.notation.str_cache

    def add_calc_term(self, calculator_or_cterm):
        if isinstance(calculator_or_cterm, CalcTerm): cterm = calculator_or_cterm
        elif isinstance(calculator_or_cterm, Calculator):
            cterm = calculator_or_cterm.build_calc_term(self.term, FakeCache())
        else: raise Exception(f"Not a Calculator / CalcTerm: {type(calculator_or_cterm)} -- {calculator_or_cterm}")
        self.calc_term = cterm
        if self.subterms:
            for asub, csub in zip(self.subterms, cterm.args):
                asub.add_calc_term(csub)

    def link_bvars(self, ctx = None):
        if ctx is None:
            ctx = []
            t = self
            while t is not None:
                ctx.extend(t for _ in t.new_bound_names)
                t = t.parent
            ctx.reverse()
        if isinstance(self.term, BVar):
            if self.term.debruijn_height <= len(ctx):
                self.bvar_link = ctx[len(ctx) - self.term.debruijn_height]
            else:
                self.bvar_link = None
        else:
            for sub in self.subterms:
                ori_size = len(ctx)
                ctx.extend(sub for _ in sub.new_bound_names)
                sub.link_bvars(ctx)
                if sub.new_bound_names: del ctx[ori_size:]

if __name__ == "__main__":
    from logic_env import LogicEnv

    env = LogicEnv()
    env.parser.parse_file("axioms_thibault")
    # term = env.parser.parse_str("if C1; a else if C2; b else c")
    term = env.parser.parse_str("sum(1 .. X, b : if b % 4 = 0 || (b % 4 = 3 && ! ((1 + X) % b = 0)) ; 1 else if b % 4 = 3 || (b % 4 = 1 && (1 + X) % b = 0) ; 0 else - 1) + 1")
    term = env.parser.parse_str("""
    loop(X, 1, x : y :
loop(y, prod(1 .. X - y, z : z + y), a : b :
      3 * a * b // (2 + b) + a)
    // factorial(X - y)
  - x)
""")
    aterm = AnnotatedTerm(term)
    print(term)
    aterm.add_notation()
    print(aterm)
    aterm.notation.auto_split_lines()
    print(aterm)
