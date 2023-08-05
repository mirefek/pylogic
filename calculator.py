from term import TermConstant, TermVariable, Term, TermApp, BVar
from logic_core import Verifier, Proof
from share_term import TermCache
import inspect

class ProofCalculator(Proof):
    pass

class ContainerValue:
    def __init__(self):
        self._env = None
        self._has_admissible_values = None

    def to_str(self, item_to_str):
        raise Exception("Not implemented")
    def get_all_items(self):
        raise Exception("Not implemented")

    def has_admissible_items(self, env):
        if env == self._env:
            return self._has_admissible_items
        self._has_admissible_items = all(
            env.is_admissible_value(x)
            for x in self.get_all_items()
        )
        self._env = env
        return self._has_admissible_items
    def __str__(self):
        return self.to_str(str)

class CalcTerm:
    def __init__(self, term):
        self.cache = dict()
        self.used_bvars = sorted(term.bound_vars, reverse = True)
    def evaluate_raw(self, bvar_values):
        raise Exception("Not implemented")
    def evaluate(self, bvar_values):
        key = tuple(bvar_values[-i] for i in self.used_bvars)
        if key in self.cache: return self.cache[key]
        res = self.evaluate_raw(bvar_values)
        self.cache[key] = res
        return res
    def as_function(self, bvar_values, arity):
        def f(*args):
            assert len(args) == arity
            return self.evaluate(bvar_values + list(args))
        return f

class CalcBvar(CalcTerm):
    def __init__(self, term):
        self.index = term.debruijn_height # default debruijn indices are from 1, here from 0
        assert self.index >= 1
        super().__init__(term)
    def evaluate_raw(self, bvar_values):
        return bvar_values[-self.index]

class CalcStep(CalcTerm):
    def __init__(self, term, f, args):
        super().__init__(term)
        self.f = f
        self.signature = term.f.signature
        self.args = args
    def evaluate_raw(self, bvar_values):
        args = (
            arg.as_function(bvar_values, numb)
            for arg, numb in zip(self.args, self.signature)
        )
        return self.f(*args)

class Calculator(Verifier):
    def __init__(self, core):
        super().__init__(core)
        self._const_to_term = dict()
        self._interpretation = {
            core.implication : (lambda x,y: not x() or y()),
            core.equality : (lambda x,y: x() == y()),
        }
        self._accepted_types = (bool, type(None))
        self._type_to_expansion = dict()

    def set_interpretation(self, termfun, python_fun):
        if self.core._strict_mode:
            raise Exception("Cannot set function interpretations in strict mode")
        assert isinstance(termfun, TermConstant)
        self._interpretation[termfun] = python_fun
        if termfun.arity == 0:
            self._const_to_term[python_fun()] = TermApp(termfun, ())

    def accept_types(self, *ts):
        if self.core._strict_mode:
            raise Exception("Cannot add accepted calculation types in strict mode")
        ts = tuple(t for t in ts if t not in self._accepted_types)
        self._accepted_types = self._accepted_types + ts

    def set_term_expansion(self, t, expansion):
        if self.core._strict_mode:
            raise Exception("Cannot set term expansion in strict mode")
        self._type_to_expansion[t] = expansion

    def is_admissible_value(self, value):
        if not isinstance(value, self._accepted_types):
            return False
        if isinstance(value, ContainerValue):
            return value.has_admissible_items(self)
        else: return True

    def get_term_value(self, term, default = None):
        assert term.f.arity == 0
        f_val = self._interpretation.get(term.f)
        if f_val is None: return default
        return f_val()

    def get_value_name(self, value):
        term = self._const_to_term.get(value, None)
        if term is not None: return str(term)
        elif isinstance(value, ContainerValue):
            return value.to_str(self.get_value_name)
        else:
            return str(value)

    def get_value_term(self, value):
        if value in self._const_to_term:
            return self._const_to_term[value]
        assert self.is_admissible_value(value), value
        #print(f"get_value_term({value})")
        expansion = self._type_to_expansion.get(type(value))
        #print(type(value), expansion, self._type_to_expansion)
        if expansion is not None: term = expansion(value)
        else: term = None
        if term is None:
            f = TermConstant((), self.get_value_name(value))
            term = TermApp(f, ())
            self._interpretation[f] = lambda : value
        self._const_to_term[value] = term
        return term

    def build_calc_term(self, term, cache):
        res = cache.get(term)
        if res is not None: return res
        if isinstance(term, BVar): res = CalcBvar(term)
        else:
            if isinstance(term.f, TermVariable):
                raise Exception(f"Cannot calculate variable '{term.f}' (in '{term}')")
            f_repr = self._interpretation.get(term.f)
            if f_repr is None:
                raise Exception(f"Calculator: constant '{term.f}' doesn't have an interpretation")
            args = [self.build_calc_term(arg, cache) for arg in term.args]
            res = CalcStep(term, f_repr, args)
        cache[term] = res
        return res
    
    def calculate(self, term, only_try = False):
        if not term.is_closed:
            if only_try: return None
            else: raise Exception(f"Calculated term '{term}' is not closed")

        try:
            term = TermCache().share(term)
            calc_term = self.build_calc_term(term, dict())
        except Exception:
            if only_try: return None
            else: raise
        try:
            val = calc_term.evaluate([])
        except AssertionError:
            if only_try: return None
            else: raise

        res = self.get_value_term(val)
        res = TermApp(self.core.equality, (term, res))
        proof = ProofCalculator()
        return self._make_thm(dict(), res, proof)

    def add_functions(self, constant_dict, *function_modules, prefix = "calc_"):
        for function_module in function_modules:
            for full_name in dir(function_module):
                if not full_name.startswith(prefix): continue
                fun = getattr(function_module, full_name)
                arity = len(inspect.signature(fun).parameters)
                name = full_name[len(prefix):]
                if name[0].isdigit():
                    signature = []
                    eval_args = []
                    while name[0].isdigit():
                        i = name.find('_')
                        numb = int(name[:i])
                        signature.append(int(name[:i]))
                        eval_args.append(name[:i] == '0')
                        name = name[i+1:]
                    assert len(signature) == arity, (name, signature)
                    signature = tuple(signature)
                    eval_args = tuple(eval_args)
                else:
                    signature = (0,)*arity
                    eval_args = (True,)*arity
                const = constant_dict[name, signature]
                self.set_interpretation(const, self._wrap_function(fun,eval_args))

    def _wrap_function(self, fun, eval_args):
        if True not in eval_args:
            return fun
        def fun2(*args):
            return fun(*(
                arg if not e else arg()
                for arg,e in zip(args, eval_args)
            ))
        return fun2

class LogicCalculation:
    def calc_true(self): return True
    def calc_false(self): return False
    def calc_null(self): return None
    def calc__neg(self, x): return not x
    def calc_00_00__or(self, x, y): return x() or y()
    def calc_00_00__and(self, x, y): return x() and y()
    def calc__xor(self, x, y): return bool(x) != bool(y)
    def calc__equiv(self, x, y): return bool(x) == bool(y)
    def calc_to_bool(self, x): return bool(x)
    def calc_to_bool1(self, x): return x is None or x
    def calc_00_00_00__if(self, c, a, b):
        if c(): return a()
        else: return b()
    def calc_00_00__require(self, c, a):
        if c(): return a()
        else: return None
    def calc_0_00__try(self, a, b):
        if a is not None: return a
        else: return b()
    def calc__is_bool(self, x): return isinstance(x, bool)
    # insane objects except null are not expected to be representable

if __name__ == "__main__":
    from parse_term import TermParser
    from logic_core import LogicCore
    core = LogicCore()
    parser = TermParser(core)
    parser.parse_file("axioms_logic")
    parser.parse_file("axioms_set")
    parser.parse_file("axioms_fun")
    calculator = Calculator(core)
    calculator.add_functions(
        parser.name_signature_to_const,
        LogicCalculation(),
    )
    def tt(s):
        return parser.parse_str(s)
    print(calculator.calculate(tt("to_bool(null)")))

