from term import Term, Substitution, get_unused_name
from logic_core import LogicCore, AssumptionLabel, DefinedConstant
from parse_term import TermParser
from unification import Unification
from pytheorem import Theorem
from basic_impl import BasicImpl
from rewriter import Rewriter
from pattern_lookup import PatternLookupImpl
from goal_context import GoalEnv
from tactics import Tactics
from term import BVar, TermApp
from calculator import Calculator, LogicCalculation
from calc_set_fun import SetCalculation, FunCalculation, BinderCalculation, MathSet, MathFun, MathNumber
from calc_numbers import CalculationNumbers, math_number_expansion

class LogicEnv:
    def __init__(self, record_proof = False):
        self.core = LogicCore(record_proof = record_proof)
        self.calculator = Calculator(self.core)
        self.calculator.accept_types(MathSet, MathFun, MathNumber)
        self.parser = TermParser(
            self.core,
            int_to_term = lambda n: self.calculator.get_value_term(MathNumber(n))
        )
        self.parser.parse_file("axioms_logic")
        self.parser.parse_file("axioms_set")
        self.parser.parse_file("axioms_fun")
        self.parser.parse_file("axioms_numbers")

        self.calculator.add_functions(
            self.parser.name_signature_to_const,
            LogicCalculation(),
            SetCalculation(),
            FunCalculation(),
            BinderCalculation(),
            CalculationNumbers(),
        )
        self.calculator.set_term_expansion(
            MathNumber,
            math_number_expansion(
                self.calculator,
                self.parser.name_signature_to_const,
            )
        )

        self._name_to_label = dict()
        self.impl_rules = dict() # name => PatternLookupImpl

        self.axioms = AxiomSet(self)
        self.constants = ConstantSet(self)
        self.basic_impl = BasicImpl(self.axioms.dummy_assump)
        self.rewriter = Rewriter(
            eq_refl = self.axioms.eq_refl,
            eq_cong = self.axioms.eq_cong,
        )
        self.tactics = Tactics(self)
        self.goal_env = GoalEnv(self)

        self.forall_intro_full = None
        self.forall_intro = None

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

        if frozen: thm = thm.freeze()
        thm = thm.impl_to_labels(label)
        return thm

    def generalize(self, thm, v, full = False):
        if isinstance(v, str):
            v = self.parser.get_var(v, 0)
        pred = thm.term
        if full:
            assert pred.f == self.constants.to_bool1
            pred = pred.args[0]
        pred = pred.substitute_free({ v : BVar(1) })
        x = TermApp(self.constants.to_bool1, (pred,))
        x = TermApp(self.constants._neg, (x,))
        x = TermApp(self.constants.example, (x,), (['x'],))
        example = x
        thm = thm.specialize({ v : example })
        if full:
            assert self.forall_intro_full != None
            x = self.forall_intro_full(PRED = pred)
        else:
            assert self.forall_intro != None
            x = self.forall_intro(PRED = pred)
        x = x.modus_ponens_basic(thm)
        return x

    def add_axiom(self, axiom_str):
        return Theorem(self, self.core.add_axiom(self.to_term(axiom_str), "in_code"))

    def add_generalize_axioms(self): # could we proven but takes too long...
        self.forall_intro_full = self.add_axiom("to_bool1(PRED(example(x : ! to_bool1(PRED(x))))) => forall(x : PRED(x))")
        self.forall_intro = self.add_axiom("PRED(example(x : ! to_bool1(PRED(x)))) => forall(x : PRED(x))")

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

class ConstantSet:
    def __init__(self, env):
        self._constant_dict = {
            const.name : const
            for const in env.parser.consts_by_age
        }
        for const in env.parser.consts_by_age:
            if isinstance(const, DefinedConstant):
                if const.def_thm is None:
                    const.def_thm = Theorem(env, const.def_core_thm)
        self._constant_signature_to_const = env.parser.name_signature_to_const
        self._eq = env.core.equality
        self._impl = env.core.implication
    def __getattr__(self, name):
        if name == "_impl": return self._constant_dict["__impl__"]
        elif name == "_eq": return self._constant_dict["__eq__"]
        res = self._constant_dict.get(name, None)
        if res is None: raise AttributeError(name)
        return res
    def __getitem__(self, key):
        name = key[0]
        signature = key[1:]
        return self._constant_signature_to_const[name, signature]

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
