from term import Term, TermFunction, Substitution, get_unused_name
from logic_core import LogicCore, AssumptionLabel
from parse_term import TermParser
from unification import Unification
from pytheorem import Theorem
from basic_impl import BasicImpl
from rewriter import Rewriter
from pattern_lookup import PatternLookupImpl
from goal_context import GoalEnv
from tactics import Tactics

class LogicEnv:
    def __init__(self):
        self.core = LogicCore()
        self.parser = TermParser(self.core)
        self.parser.parse_file("axioms_logic")
        self._name_to_label = dict()
        self.impl_rules = dict() # name => PatternLookupImpl

        self.axioms = AxiomSet(self)
        self.constants = ConstantSet(self)
        self.defs = DefinitionSet(self)
        self.basic_impl = BasicImpl(self.axioms.dummy_assump)
        self.rewriter = Rewriter(
            eq_refl = self.axioms.eq_refl,
            eq_cong = self.axioms.eq_cong,
        )
        self.tactics = Tactics(self)
        self.goal_env = GoalEnv(self)

    def add_impl_rule(self, name, *rules):
        rule_set = self.impl_rules.get(name, None)
        if rule_set is None:
            rule_set = PatternLookupImpl(
                get_new_var = self.get_locally_fresh_var
            )
        rule_set = rule_set.add_rule(*rules)
        self.impl_rules[name] = rule_set

    def get_locally_fresh_var(self, v, used_names):
        name = get_unused_name(v.name, used_names)
        return self.parser.get_var(name, v.arity)

    def split_impl(self, term):
        assert term.f == self.core.implication, term
        return term.args
    def split_eq(self, term):
        assert term.f == self.core.equality, term
        return term.args

    def to_term(self, term, allow_binders = False):
        if isinstance(term, Term): return term
        if isinstance(term, str):
            if allow_binders:
                return self.parser.parse_str(term, with_binders = True)[1]
            else:
                return self.parser.parse_str(term, with_binders = False)
        else:
            raise Exception(f"Expected Term, got {type(term)}")
    def to_label(self, label):
        if isinstance(label, AssumptionLabel): return label
        else:
            assert isinstance(label, str)
            name = label
            label = self._name_to_label.get(name)
            if label is None:
                label = AssumptionLabel(name)
                self._name_to_label[name] = label
            return label

    def hypothesis(self, label, term, frozen = True):
        assert isinstance(label, (str, AssumptionLabel))
        term = self.to_term(term)
        thm = self.basic_impl.refl(term)
        label = self.to_label(label)

        if frozen: thm.frozen_vars = term.free_vars
        thm = thm.impl_to_labels(label)
        return thm

class AxiomSet:
    def __init__(self, env):
        self._env = env
        self._core_dict = env.parser.name_to_axiom
        self._axiom_dict = dict()
    def __getattr__(self, name):
        res = self._axiom_dict.get(name, None)
        if res is not None: return res
        res = self._core_dict.get(name, None)
        if res is None: raise AttributeError(name)
        res = Theorem(self._env, res)
        self._axiom_dict[name] = res
        return res

class DefinitionSet:
    def __init__(self, env):
        self._env = env
        self._constant_dict = {
            name : const
            for (name, sgn), const in env.parser.name_signature_to_const.items()
        }
        self._constant_to_core = env.parser.const_to_definition
        self._cache = dict()
        self._axiom_dict = dict()
    def __getattr__(self, name):
        res = self[name]
        if res is None: raise AttributeError(f"No definition of '{name}'")
        return res
    def __getitem__(self, constant):
        res = self._cache.get(constant, None)
        if res is not None: return res
        if isinstance(constant, str):
            name = constant
            constant = self._constant_dict.get(name, None)
            if constant is None: return None
            res = self._cache.get(constant, None)
            if res is not None:
                self._cache[name] = res
                return res
        else: name = None
        core_thm = self._constant_to_core.get(constant, None)
        if core_thm is None: return None
        res = Theorem(self._env, core_thm)
        if name is not None: self._cache[name] = res
        self._cache[constant] = res
        return res

class ConstantSet:
    def __init__(self, env):
        self._constant_dict = {
            name : const
            for (name, sgn), const in env.parser.name_signature_to_const.items()
        }
        self._eq = env.core.equality
        self._impl = env.core.implication
    def __getattr__(self, name):
        if name == "_impl": return self._constant_dict["__impl__"]
        elif name == "_eq": return self._constant_dict["__eq__"]
        res = self._constant_dict.get(name, None)
        if res is None: raise AttributeError(name)
        return res

# TESTS
            
if __name__ == "__main__":
    env = LogicEnv()

    hyp = env.hypothesis('hyp', "X = Y", frozen = False)
    print(hyp)
    print()
    x = hyp.symm
    print(x)
    print()
    x = x.to_impl()
    print(x)
    print()
