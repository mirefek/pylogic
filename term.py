import re

class TermFunction:
    def __init__(self, signature, name = None, get_name = None):
        if name is None:
            assert get_name is not None
            self.get_name = get_name
        else:
            assert get_name is None
            self.get_name = lambda: name
        self.notation = None
        self._signature = tuple(signature)
        self._to_term = None

    def __str__(self):
        return self.get_name()
    def __repr__(self):
        return f"{type(self).__name__}({self})"
    def to_term(self):
        if self._to_term is not None: return self._to_term
        assert not any(self.signature)
        self._to_term = TermApp(self, tuple(
            BVar(i) for i in range(self.arity, 0, -1)
        ))
        return self._to_term

    @property
    def signature(self):
        return self._signature
    @property
    def arity(self):
        return len(self._signature)
    @property
    def name(self):
        return self.get_name()
    
    def __call__(self, *args):
        term_args = []
        bound_names = []
        for arg,n in zip(args,self.signature):
            if isinstance(arg, Term):
                term_args.append(arg)
                bound_names.append(('?b',)*n)
            elif callable(arg):
                assert arg.__code__.co_argcount == n
                arg_names = arg.__code__.co_varnames[:n]
                vs = [TermVariable(0) for _ in range(n)]
                tvs = [v.to_term() for v in vs]
                t = arg(*tvs)
                assert isinstance(t, Term)
                if n > 0:
                    bvs = [BVar(n-i) for i in range(n)]
                    t = t.substitute_free(dict(zip(vs, bvs)))
                term_args.append(t)
                bound_names.append(arg_names)
            else: raise Exception(f"Cannot call a term function on {type(arg)}")

        return TermApp(self, tuple(term_args), bound_names = tuple(bound_names))

anon_counter = 0

class TermConstant(TermFunction):
    def __init__(self, signature, name = None):
        global anon_counter
        if name is None:
            name = "?c"+str(anon_counter)
            anon_counter+=1
        super().__init__(signature, name)

class TermVariable(TermFunction):
    def __init__(self, arity, name = None):
        global anon_counter
        if name is None:
            name = "?v"+str(anon_counter)
            anon_counter+=1
        super().__init__((0,)*arity, name)

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

    def substitute_free(self, subst_d):
        return Substitution(subst_d).run(self)
    def substitute_bvars(self, args, natural_order = True):
        subst_env = Substitution(dict())
        if natural_order:
            if not isinstance(args, (list, tuple)): args = tuple(args)
            subst_env.subst_l = [None]+list(reversed(args))
        else:
            subst_env.subst_l = list(args)
        if len(subst_env.subst_l) <= self.debruijn_height:
            subst_env.subst_l.extend(
                BVar(i) for i in range(len(subst_env.subst_l), self.debruijn_height+1)
            )
        subst_env._cache_subst_bound = dict()
        return subst_env._substitute_bound(self, 0)

    def rename_vars(self, subst_d):
        assert all(
            isinstance(v1, TermVariable) and v1.signature == v2.signature
            for v1,v2 in subst_d.items()
        )
        return self._rename_vars(subst_d, cache = dict())

    def get_ordered_free_vars(self, res = None):
        if res is None:
            res = []
        if not self.free_vars.difference(res): return res
        if self.is_free_var and self.f not in res:
            res.append(self.f)
        for arg in self.args:
            arg.get_ordered_free_vars(res)
        return res

    def __str__(self):
        return self.to_str()
    def __repr__(self):
        return f"Term({self.to_str()})"

    def __iter__(self):
        return iter(self.args)
    def __getitem__(self, i):
        return self.args[i]
    def __len__(self):
        return len(self.args)

class BVar(Term):
    def __init__(self, debruijn_index):
        self.f = None
        self.args = ()
        self.debruijn_height = debruijn_index
        self.free_vars = frozenset()
        self.bound_vars = frozenset((debruijn_index,))

    def to_str(self, bound_names = (), taken_names = None, **notation_kwargs):
        i = len(bound_names) - self.debruijn_height
        if i >= 0: return bound_names[i]
        else: return f"^{-i}^"

    def _rename_vars(self, subst_d, cache):
        return self

    @property
    def is_free_var(self): return False
    @property
    def is_const(self): return False
    @property
    def is_closed(self): return False

    def equals_to(self, other, cache = None):
        return isinstance(other, BVar) and self.debruijn_height == other.debruijn_height

class TermApp(Term):
    def __init__(self, f, args = (), bound_names = None):
        assert all(isinstance(arg, Term) for arg in args)
        assert len(args) == f.arity

        self.f = f
        self.args = tuple(args)
        self.debruijn_height = 0
        if bound_names is None:
            self.bound_names = tuple(('?b',)*n for n in f.signature)
        else: self.bound_names = bound_names
        for arg, numb in zip(args, f.signature):
            assert isinstance(arg, Term)
            self.debruijn_height = max(self.debruijn_height, arg.debruijn_height - numb)
        self._free_vars = None
        self._bound_vars = None

    def to_str(self, bound_names = (), taken_names = None, **notation_kwargs):
        if taken_names is None:
            taken_names = set(x.name for x in self.free_vars)
        if self.f.notation is not None:
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

    def _rename_vars(self, subst_d, cache):
        res = cache.get(self)
        if res is not None: return res
        free_vars = self.free_vars
        if len(free_vars) < len(subst_d):
            if all(v not in subst_d for v in free_vars): return self
        else:
            if all(v not in free_vars for v in subst_d.keys): return self
        f = self.f
        f = subst_d.get(f,f)
        args = tuple(
            arg._rename_vars(subst_d, cache)
            for arg in self.args
        )
        return TermApp(f, args, self.bound_names)
        cache[self] = res
        return res

    @property
    def is_free_var(self): return isinstance(self.f, TermVariable)
    @property
    def is_const(self): return isinstance(self.f, TermConstant)
    @property
    def is_closed(self): return self.debruijn_height == 0

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
        self._bound_vars = set()
        for arg,numb in zip(self.args, self.f.signature):
            for bv in arg.bound_vars:
                if bv > numb: self._bound_vars.add(bv - numb)
        return self._bound_vars

    def equals_to(self, other, cache = None):
        if self == other: return True
        if cache is None: cache = set()
        if (self, other) in cache: return True
        if self.f != other.f: return False
        if self.debruijn_height != other.debruijn_height: return False
        if not all(arg1.equals_to(arg2) for arg1, arg2 in zip(self.args, other.args)):
            return False
        cache.add((self, other))
        return True

class Substitution:
    def __init__(self, subst_d):
        self.subst_d = subst_d
        self._subst_vars = set(subst_d.keys())
        self._subst_nc_vars = set()
        for v,t in subst_d.items():
            if not (t.debruijn_height <= v.arity):
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
            res = TermApp(term.f, args, bound_names = term.bound_names)
        else:
            assert term.is_free_var
            val = self.subst_d[term.f]
            if term.f.arity == 0 or val.debruijn_height == 0:
                if val.debruijn_height > term.f.arity:
                    val = self.debruijn_shift(val, term.f.arity, depth)
                res = val
            else:
                used_boundvars = val.bound_vars
                args = [None] * (max(used_boundvars | {0})+1)
                changed = False
                for v in used_boundvars:
                    if v <= term.f.arity:
                        arg = self.run(term.args[term.f.arity-v], depth)
                    else:
                        arg = BVar(depth+v)
                    args[v] = arg
                    if not isinstance(arg, BVar) or arg.debruijn_height != v:
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
        if term.debruijn_height <= depth: return term
        res = self._cache_subst_bound.get((term, depth), None)
        if res is not None: return res

        if isinstance(term, BVar):
            res = self.subst_l[term.debruijn_height - depth]
            res = self.debruijn_shift(res, 0, depth)
        else:
            args = tuple(
                self._substitute_bound(arg, depth+numb)
                for arg, numb in zip(term.args, term.f.signature)
            )
            res = TermApp(term.f, args, bound_names = term.bound_names)

        self._cache_subst_bound[term, depth] = res
        return res

    def debruijn_shift(self, term, depth, shift):
        if term.debruijn_height <= depth: return term
        res = self._cache_shift.get((term, depth, shift), None)
        if res is not None: return res

        elif isinstance(term, BVar):
            res = BVar(term.debruijn_height + shift)
        else:
            args = tuple(
                self.debruijn_shift(arg, depth+numb, shift)
                for arg, numb in zip(term.args, term.f.signature)
            )
            res = TermApp(term.f, args, bound_names = term.bound_names)

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
