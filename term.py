import re

class TermFunction:
    def __init__(self, signature, name = None):
        self.name = name
        self.notation = None
        self._signature = tuple(signature)

    def __str__(self):
        return self.name
    def __repr__(self):
        return f"TermFunction({self})"

    @property
    def signature(self):
        return self._signature
    @property
    def arity(self):
        return len(self._signature)

class TermConstant(TermFunction):
    def __init__(self, signature, name = "?c"):
        super().__init__(signature, name)
    def __repr__(self):
        return f"TermConstant({self})"

class TermVariable(TermFunction):
    def __init__(self, arity, name = "?v"):
        super().__init__((0,)*arity, name)
    def __repr__(self):
        return f"TermVariable({self})"
    def to_term(self):
        return Term(self, tuple(Term(i) for i in range(self.arity, 0, -1)))

num_suffix_regex = re.compile("[0-9]+$")
def next_names(first_name):
    match = num_suffix_regex.search(first_name)
    if match is not None:
        num = match.group()
        num_len = len(num)
        num = int(num)
        first_name = first_name[:match.start()]
    else:
        num = -1
        num_len = 1

    start_letter = None
    if len(first_name) == 1:
        if ord(first_name) >= ord('a') and ord(first_name) <= ord('z'):
            start_letter = 'a'
        elif ord(first_name) >= ord('A') and ord(first_name) <= ord('Z'):
            start_letter = 'A'

    if start_letter is not None:
        while True:
            start_letter_i = ord(start_letter)
            start_i = ord(first_name) - start_letter_i
            for i in range(start_i, start_i+26):
                c = chr(start_letter_i + i%26)
                if num < 0: yield c
                else: yield "{}{:0{}}".format(c, num, num_len)
            start_i = 0
            num += 1
    else:
        while True:
            if num < 0: yield first_name
            else: yield "{}{:0{}}".format(first_name, num, num_len)
            num += 1

def get_unused_name(first_name, used):
    for name in next_names(first_name):
        if name not in used: return name

class Term:
    def __init__(self, f_or_debruin, args = (), bound_names = None):
        self._free_vars = None
        self._bound_vars = None
        if isinstance(f_or_debruin, TermFunction):
            f = f_or_debruin
            assert all(isinstance(arg, Term) for arg in args)
            assert len(args) == f.arity

            self.f = f
            self.args = tuple(args)
            self.debruin_height = 0
            if bound_names is None:
                self.bound_names = tuple(('?b',)*n for n in f.signature)
            else: self.bound_names = bound_names
            for arg, numb in zip(args, f.signature):
                assert isinstance(arg, Term)
                self.debruin_height = max(self.debruin_height, arg.debruin_height - numb)
        else:
            assert isinstance(f_or_debruin, int) and f_or_debruin > 0
            assert not args

            self.f = None
            self.args = ()
            self.debruin_height = f_or_debruin

    def substitute_free(self, subst_d):
        return Substitution(subst_d).run(self)
    def substitute_bvars(self, args, natural_order = True):
        subst_env = Substitution(dict())
        if natural_order:
            if not isinstance(args, (list, tuple)): args = tuple(args)
            subst_env.subst_l = [None]+list(reversed(args))
        else:
            subst_env.subst_l = list(args)
        if len(subst_env.subst_l) <= self.debruin_height:
            subst_env.subst_l.extend(
                Term(i) for i in range(len(subst_env.subst_l), self.debruin_height+1)
            )
        subst_env._cache_subst_bound = dict()
        return subst_env._substitute_bound(self, 0)

    def equals_to(self, other, cache = None):
        if self == other: return True
        if cache is None: cache = set()
        if (self, other) in cache: return True
        if self.f != other.f: return False
        if self.debruin_height != other.debruin_height: return False
        if not all(arg1.equals_to(arg2) for arg1, arg2 in zip(self.args, other.args)):
            return False
        cache.add((self, other))
        return True

    @property
    def is_free_var(self):
        return self.f is not None and isinstance(self.f, TermVariable)
    @property
    def is_const(self):
        return self.f is not None and isinstance(self.f, TermConstant)
    @property
    def is_bvar(self):
        return self.f is None
    @property
    def is_closed(self):
        return self.debruin_height == 0

    @property
    def free_vars(self):
        if self._free_vars is not None: return self._free_vars
        self._free_vars = set()
        if self.is_free_var: self._free_vars.add(self.f)
        for arg in self.args:
            self._free_vars.update(arg.free_vars)
        return self._free_vars
    @property
    def bound_vars(self):
        if self._bound_vars is not None: return self._bound_vars
        if self.is_bvar:
            self._bound_vars = { self.debruin_height }
        else:
            self._bound_vars = set()
            for arg,numb in zip(self.args, self.f.signature):
                for bv in arg.bound_vars:
                    if bv > numb: self._bound_vars.add(bv - numb)
        return self._bound_vars

    def get_ordered_free_vars(self, res = None):
        if res is None:
            res = []
        if not self.free_vars.difference(res): return res
        if self.is_free_var and self.f not in res:
            res.append(term.f)
        for arg in args:
            get_ordered_free_vars(res)
        return res

    def to_str(self, bound_names = (), taken_names = None, **notation_kwargs):
        if taken_names is None:
            taken_names = set(x.name for x in self.free_vars)
        if self.is_bvar:
            i = len(bound_names) - self.debruin_height
            if i >= 0: return bound_names[i]
            else: return f"^{-i}^"
        elif self.f.notation is not None:
            return self.f.notation.objects_to_str(
                self.args,
                bound_names = bound_names, taken_names = taken_names,
                **notation_kwargs,
            )
        elif not self.args:
            return str(self.f)
        else:
            arg_strings = []
            for arg, bns in zip(self.args, self.bound_names):
                bns_fresh = []
                for bn in bns:
                    bn_fresh = get_unused_name(bn, taken_names)
                    bns_fresh.append(bn_fresh)
                    taken_names.add(bn_fresh)
                arg_string = arg.to_str(bound_names+tuple(bns_fresh), taken_names)
                taken_names.difference_update(bns_fresh)
                arg_strings.append(' : '.join(bns_fresh+[arg_string]))

            return str(self.f)+'('+', '.join(arg_strings)+')'

    def __str__(self):
        return self.to_str()
    def __repr__(self):
        return f"Term({self.to_str()})"

class Substitution:
    def __init__(self, subst_d):
        self.subst_d = subst_d
        self._subst_vars = set(subst_d.keys())
        self._subst_nc_vars = set()
        for v,t in subst_d.items():
            if not (t.debruin_height <= v.arity):
                self._subst_nc_vars.add(v)
        self._cache_run = dict()
        self._cache_shift = dict()

    def run(self, term, depth = 0):
        if not (self._subst_nc_vars & term.free_vars): depth = 0
        res = self._cache_run.get((term, depth), None)
        if res is not None: return res
            
        if not (self._subst_vars & term.free_vars):
            res = term
        elif term.f not in self.subst_d: # term cannot be bound var -- handled before
            args = tuple(
                self.run(arg, depth+numb)
                for arg,numb in zip(term.args, term.f.signature)
            )
            res = Term(term.f, args, bound_names = term.bound_names)
        else:
            assert term.is_free_var
            val = self.subst_d[term.f]
            if term.f.arity == 0 or val.debruin_height == 0:
                if val.debruin_height > term.f.arity:
                    val = self.debruin_shift(val, term.f.arity, depth)
                res = val
            else:
                used_boundvars = val.bound_vars
                args = [None] * (max(used_boundvars | {0})+1)
                changed = False
                for v in used_boundvars:
                    if v <= term.f.arity:
                        arg = self.run(term.args[v-1], depth)
                    else:
                        arg = Term(depth+v)
                    args[v] = arg
                    if not arg.is_bvar or arg.debruin_height != v:
                        changed = True

                if not changed:
                    res = val
                else:
                    self.subst_l = args
                    self._cache_subst_bound = dict()
                    res = self._substitute_bound(val, 0)
                    del self.subst_l
                    del self._cache_subst_bound

        self._cache_run[term, depth] = res
        return res

    def _substitute_bound(self, term, depth):
        if term.debruin_height <= depth: return term
        res = self._cache_subst_bound.get((term, depth), None)
        if res is not None: return res

        if term.is_bvar:
            res = self.subst_l[term.debruin_height - depth]
            res = self.debruin_shift(res, 0, depth)
        else:
            args = tuple(
                self._substitute_bound(arg, depth+numb)
                for arg, numb in zip(term.args, term.f.signature)
            )
            res = Term(term.f, args, bound_names = term.bound_names)

        self._cache_subst_bound[term, depth] = res
        return res

    def debruin_shift(self, term, depth, shift):
        if term.debruin_height <= depth: return term
        res = self._cache_shift.get((term, depth, shift), None)
        if res is not None: return res

        elif term.is_bvar:
            res = Term(term.debruin_height + shift)
        else:
            args = tuple(
                self.debruin_shift(arg, depth+numb, shift)
                for arg, numb in zip(term.args, term.f.signature)
            )
            res = Term(term.f, args, bound_names = term.bound_names)

        self._cache_shift[term, depth, shift] = res
        return res

def compose_substitutions(*substs):
    # try trivial
    only_nontriv = None
    for subst in substs:
        if not subst: continue
        if only_nontriv is None: break
        only_nontriv = subst
    else:
        if only_nontriv: return only_nontriv
        else: return dict()

    # compose from the back
    substs = list(substs)
    substs.reverse()
    res = dict(substs[0])
    for subst in substs[1:]:
        if not subst: continue
        if not res:
            res = subst
            continue
        res2 = {
            v : t.substitute_free(res)
            for v,t in subst.items()
        }
        for v,t in res.items():
            res2.setdefault(v,t)
        res = res2

    return res
