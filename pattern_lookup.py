import itertools
from term import Term
from unification import Unification

class LookupNode:
    pass

class LookupNodeResult(LookupNode):
    def __init__(self, result = ()):
        self._result = tuple(result)
    def __iter__(self):
        return iter(self._result)
    def union(self, other):
        return LookupNodeResult(self._result + other._result)

class LookupNodeByTerm(LookupNode):
    def __init__(self, universal = (), subpatterns = None):
        assert len(universal) <= 1
        self._universal = universal
        if subpatterns is None:
            subpatterns = dict()
        self._subpatterns = subpatterns

    @classmethod
    def take_term_iter(cls, it, term):
        for x in it:
            yield from x.take_term(term)
    def take_term(self, term):
        res = self._subpatterns.get(term.f, None)
        if res is None: return iter(self._universal)

        res = [res]
        for arg in term.args:
            res = self.take_term_iter(res, arg)
        if self._universal is not None:
            res = itertools.chain(res, self._universal)
        return res

    def union(self, other):
        if not other._universal: universal = self._universal
        elif not self._universal: universal = other._universal
        else:
            universal = [self._universal[0].union(other._universal[0])]
        if not other._subpatterns:
            subpatterns = self._subpatterns
        elif not self._subpatterns:
            subpatterns = other._subpatterns
        else:
            subpatterns = dict(self._subpatterns)
            for f,other_subpat in other._subpatterns.items():
                subpat = subpatterns.setdefault(f, other_subpat)
                if subpat != other_subpat:
                    subpatterns[f] = subpat.union(other_subpat)
        return LookupNodeByTerm(universal, subpatterns)

class PatternLookup:
    def __init__(self, get_new_var = None, frozen_vars = (), root_node = None):
        self._get_new_var = get_new_var
        self._frozen_vars = set(frozen_vars)
        if root_node is None:
            root_node = LookupNodeByTerm()
        self._root_node = root_node

    # building
    def _make_node(self, term, value):
        if not isinstance(value, LookupNode):
            value = LookupNodeResult([value])
        if term.f.is_free_variable and term.f not in self._frozen_vars:
            return LookupNodeByTerm(universal = [value])
        res = value
        for arg in reversed(term.args):
            res = self._make_node(arg, res)
        return LookupNodeByTerm(subpatterns = { term.f : res })

    def _replace(self, frozen_vars = None, root_node = None):
        if frozen_vars is None: frozen_vars = self._frozen_vars
        if root_node is None: root_node = self._root_node
        constr = type(self)
        return constr(
            get_new_var = self._get_new_var,
            frozen_vars = frozen_vars,
            root_node = root_node
        )

    def add_pattern(self, term, data):
        new_node = self._make_node(term, (term, data))
        return self._replace(self._frozen_vars, self._root_node.union(new_node))
    def union(self, other):
        return self._replace(root_node = self._root_node.union(other._root_node))
    def set_frozen(self, frozen_vars):
        return self._replace(frozen_vars = frozen_vars)

    def _final_unify(self, term, match_term, match_term_vars):
        unification = Unification(frozen = (self._frozen_vars, None))
        unification.add_requirement(match_term,0, term,1)
        if unification.run():
            subst,_ = unification.export_substitutions(
                (match_term_vars, term.free_vars),
                self._get_new_var,
            )
            return subst
        else:
            return None

    def process_input(self, term):
        assert isinstance(term, Term)
        return term
    def final_step(self, term, match_term):
        subst = self._final_unify(term, match_term, match_term.free_vars)
        return subst, data

    # search
    def find_iter(self, pattern_input):
        term = self.process_input(pattern_input)
        res = self._root_node.take_term(term)
        res = itertools.chain.from_iterable(res)
        for match_term, data in res:
            res = self.final_step(pattern_input, match_term, data)
            if res is not None: yield res
    def find_all(self, term):
        return list(self.find_iter(term))
    def find_first(self, term):
        return next(itertools.chain(self.find_iter(term), [None]))

    def __or__(self, other):
        return self.union(other)

class PatternLookupRewrite(PatternLookup):
    def add_rule(self, rule):
        term = rule.term
        a, b = rule._env.split_eq(rule.term)
        return self.add_pattern(a, rule)
    def final_step(self, term, match_term, rule):
        subst = self._final_unify(term, match_term, rule.free_vars)
        if subst is None: return None
        return rule.specialize(subst)

class PatternLookupImpl(PatternLookup):
    def add_rule(self, *rules):
        a, _ = rules[0]._env.split_impl(rules[0].term)
        for thm in rules[1:]:
            a2, _ = thm._env.split_impl(thm.term)
            assert a2.equals_to(a)
        return self.add_pattern(a, rules)
    def process_input(self, thm):
        return thm.term
    def final_step(self, thm, match_term, rules):
        rules_vars = set().union(*(rule.free_vars for rule in rules))
        subst = self._final_unify(thm.term, match_term, rules_vars)
        if subst is None: return None
        res = tuple(
            rule.specialize(subst).modus_ponens_basic(thm)
            for rule in rules
        )
        if len(res) == 1: return res[0]
        else: return res
