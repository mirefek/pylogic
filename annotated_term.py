from term import Term, TermApp, BVar, get_unused_name
from calculator import Calculator, CalcTerm
from share_term import TermCache
from simple_log import simple_log

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

class InconsistentValueError(Exception):
    def __init__(self, input_names, input_vals, ori, new):
        self.inputs = list(zip(input_names, input_vals))
        self.ori = ori
        self.new = new
    def __str__(self):
        lines = ["Inconsistent value"]
        if self.inputs:
            lines.append('  '+', '.join(f"{v} = {val}" for v,val in self.inputs))
        lines.append(f"  ori = {self.ori}, new = {self.new}")
        return '\n'.join(lines)

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

    def add_calc_term(self, calculator, cterm = None):
        self.calculator = calculator
        if cterm is None: 
            cterm = calculator.build_calc_term(self.term, FakeCache())
        self.calc_term = cterm
        if self.subterms:
            for asub, csub in zip(self.subterms, cterm.args):
                asub.add_calc_term(calculator, csub)

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

    def add_calc_bvars(self, bvars):
        aterm = self
        calc_bvars = set(self.calc_term.used_bvars)
        bvars = bvars - calc_bvars
        if not bvars: return # we already have all necessary bound variables

        while True:
            cterm = aterm.calc_term
            top_term = aterm.term
            cache0 = cterm.cache0
            cterm.cache0 = dict()
            cterm.cache = dict()
            cterm.used_bvars = sorted(bvars | calc_bvars)
            if aterm.parent is None: break
            shift = len(aterm.new_bound_names)
            aterm = aterm.parent
            calc_bvars = set(aterm.calc_term.used_bvars)
            bvars = set(x - shift for x in bvars if x > shift) - calc_bvars
            if not bvars: break

        for bvar_values in cache0.keys():
            cterm.evaluate(bvar_values)

    def calc_replace(self, term): # replaces itself with another term, checking that calculations fit

        self.add_calc_bvars(term.bound_vars)

        aterm = AnnotatedTerm(term, bound_names = self.bound_names)
        aterm.add_calc_term(self.calculator)

        cterm0 = self.calc_term
        cterm1 = aterm.calc_term
        for args, value0 in cterm0.cache0.items():
            value1 = cterm1.evaluate(args)
            if value0 != value1:
                key = tuple(args[-i] for i in cterm0.used_bvars)
                raise InconsistentValueError(
                    input_names = [self.bound_names[-x] for x in cterm0.used_bvars],
                    input_vals = key,
                    ori = value0,
                    new = value1,
                )

        # exchange in the term
        aterm.new_bound_names = self.new_bound_names
        if self.parent is not None:
            self.parent.replace_subterm(self.parent_i, aterm)
        aterm.add_notation()

        for x in aterm.path_to_root(): x.notation.calculate_str()
        aterm.link_bvars()

        return aterm

    def abstract_subterms(self, subterms, make_var):
        value_to_var = dict()
        term_cache = TermCache()
        term = self._abstract_subterms(0, value_to_var, term_cache, subterms, make_var)
        var_to_value = {v:val for (val,arity),v in value_to_var.items()}
        return term, var_to_value
    def _abstract_subterms(self, debruijn_depth, value_to_var, term_cache, subterms, make_var):
        if self in subterms:
            # find bound variables that need to be captured
            # e.g. 6,5,1
            captured_vars = sorted(
                filter(lambda x: x <= debruijn_depth, self.term.bound_vars),
                reverse = True
            )
            # substitute them with consecutive bvars
            # e.g. [3,2,_,_,_,1]
            if len(captured_vars) != debruijn_depth:
                bvar_subst = [None]*(debruijn_depth+1)
                n = len(captured_vars)
                for i,x in enumerate(captured_vars):
                    bvar_subst[x] = BVar(n-i)
                if len(bvar_subst) <= self.term.debruijn_height:
                    shift = debruijn_depth - len(captured_vars)
                    bvar_subst.extend(
                        BVar(i-shift) for i in range(debruijn_depth+1, self.term.debruijn_height+1)
                    )
                    simple_log("shift:", shift)
                    simple_log("bvar_subst:", bvar_subst)
                value = self.term.substitute_bvars(bvar_subst, natural_order = False)
            else:
                value = self.term
            value = term_cache.share(value)

            # find a corresponding variable
            arity = len(captured_vars)
            if (value,arity) in value_to_var:
                v = value_to_var[value,arity]
            else:
                v = make_var(len(captured_vars))
                value_to_var[value,arity] = v
            return TermApp(v, tuple(BVar(x) for x in captured_vars))
        else:
            # recurse on direct subterms (args)
            args_res = tuple(
                arg._abstract_subterms(
                    debruijn_depth+len(arg.new_bound_names),
                    value_to_var, term_cache, subterms, make_var
                )
                for arg in self.subterms
            )
            # case: nothing happened
            if all(arg_res == arg.term for arg_res,arg in zip(args_res, self.subterms)):
                return self.term
            else: # case: term has changed
                bound_names = tuple(
                    tuple(arg.new_bound_names)
                    for arg in self.subterms
                )
                return TermApp(self.term.f, args_res, bound_names)

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
