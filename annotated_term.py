from term import Term, TermApp, BVar, get_unused_name

class ATNotation:
    def __init__(self, aterm):
        self.aterm = aterm
        self.term = aterm.term
        self.parts = []
        self.spaces = []
        self.arg_i_to_part_i = []

        if isinstance(self.term, BVar):
            self.parts.append(self.term.debruijn_height)
            return

        if self.term.f.notation is not None:
            self.build_operator_syntax()
        else: self.build_function_syntax()

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
            self.parts.append((subaterm, i))
            self.spaces.append(' ')
            self.parts.append(':')
            self.spaces.append(' ')

        self.arg_i_to_part_i.append(len(self.parts))
        self.parts.append(subaterm)

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

    def part_to_str(self, part):
        if isinstance(part, str): return part
        elif isinstance(part, int):
            return self.aterm.bound_names[-part]
        elif isinstance(part, tuple):
            subaterm,vi = part
            return subaterm.new_bound_names[vi]
        elif isinstance(part, AnnotatedTerm):
            return part.notation.str_cache

    def calculate_str(self):
        n = len(self.parts)
        assert len(self.spaces) == n-1, (self.parts, self.spaces)
        substrs = [None]*(len(self.parts)*2-1)
        substrs[::2] = [self.part_to_str(part) for part in self.parts]
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

        parts = [self.part_to_str(part) for part in self.parts]
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
                if isinstance(self.parts[idx+1], AnnotatedTerm): n = next_indent
                else: n = indent
                self.spaces[idx] = '\n'+' '*n
            n += after_size
        self.calculate_str()

class AnnotatedTerm:
    def __init__(self, term, parent = None):
        self.term = term
        if parent is None:
            self.parent, self.parent_i = None, None
            self.new_bound_names = []
            self.bound_names = []
            self.taken_names = set(fv.name for fv in term.free_vars)
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

if __name__ == "__main__":
    from logic_env import LogicEnv

    env = LogicEnv()
    # term = env.parser.parse_str("if C1; a else if C2; b else c")
    term = env.parser.parse_str("sum(1 .. X, b : if b % 4 = 0 || (b % 4 = 3 && ! ((1 + X) % b = 0)) ; 1 else if b % 4 = 3 || (b % 4 = 1 && (1 + X) % b = 0) ; 0 else - 1) + 1")
    aterm = AnnotatedTerm(term)
    print(term)
    aterm.add_notation()
    print(aterm)
    aterm.notation.auto_split_lines()
    print(aterm)
