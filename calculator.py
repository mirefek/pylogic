from term import TermConstant, TermVariable, Term, TermApp, BVar
from logic_core import Verifier
from share_term import term_to_instr_list
import inspect

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
    def __init__(self, used_bvars):
        self.cache = dict()
        self.used_bvars = used_bvars
    def evaluate_raw(self, bvar_values):
        raise Exception("Not implemented")
    def evaluate(self, bvar_values, arity = 0):
        key = tuple(
            v for i,v in enumerate(bvar_values)
            if self.used_bvars & (1 << (i+arity))
        ), arity
        res = self.cache.get(key, None)
        assert not (self.used_bvars >> (arity + len(bvar_values)))
        if res is not None: return res
        if arity == 0:
            res = self.evaluate_raw(bvar_values)
        else:
            def res(*args):
                assert len(args) == arity
                args = tuple(reversed(args))
                return self.evaluate(args + bvar_values)
        self.cache[key] = res
        return res

class CalcBvar(CalcTerm):
    def __init__(self, index):
        self.index = index-1 # default debruijn indices are from 1, here from 0
        assert self.index >= 0
        super().__init__(1 << self.index)
    def evaluate_raw(self, bvar_values):
        return bvar_values[self.index]

class CalcStep(CalcTerm):
    def __init__(self, f, signature, args):
        used_bvars = 0
        for numb, arg in zip(signature, args):
            used_bvars |= (arg.used_bvars >> numb)
        super().__init__(used_bvars)
        self.f = f
        self.signature = signature
        self.args = args
    def evaluate_raw(self, bvar_values):
        args = [
            arg.evaluate(bvar_values, arity = numb)
            for arg, numb in zip(self.args, self.signature)
        ]
        return self.f(*args)

class Calculator(Verifier):
    def __init__(self, core):
        super().__init__(core, "calculator")
        self._const_to_term = dict()
        self._interpretation = {
            core.implication : (lambda x,y: not x or y),
            core.equality : (lambda x,y: x == y),
        }
        self._accepted_types = (bool, type(None))

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

    def is_admissible_value(self, value):
        if not isinstance(value, self._accepted_types):
            return False
        if isinstance(value, ContainerValue):
            return value.has_admissible_items(self)
        else: return True

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
        f = TermConstant((), self.get_value_name(value))
        term = TermApp(f, ())
        self._interpretation[f] = lambda : value
        self._const_to_term[value] = term
        return term

    def calculate(self, term, only_try = False):
        if not term.is_closed:
            if only_try: return None
            else: raise Exception(f"Calculated term '{term}' is not closed")
        instr_list, terms = term_to_instr_list(term)
        calc_terms = []
        for f_args in instr_list:
            f = f_args[0]
            if isinstance(f, int):
                calc_terms.append(CalcBvar(f))
            else:
                if isinstance(f, TermVariable):
                    if only_try: return None
                    raise Exception(f"Cannot calculate variable '{f}' (in '{term}')")
                f_repr = self._interpretation.get(f, None)
                if f_repr is None:
                    if only_try: return None
                    raise Exception(f"Calculator: constant '{f}' doesn't have an interpretation")
                args = [calc_terms[i] for i in f_args[1:]]
                calc_terms.append(CalcStep(f_repr, f.signature, args))

        calc_term = calc_terms[-1]
        try:
            val = calc_term.evaluate(())
        except AssertionError:
            if only_try: return None
            else: raise

        res = self.get_value_term(val)
        calc_term = TermApp(self.core.equality, (term, res))
        origin = term.f
        return self._make_thm(dict(), calc_term, origin)

    def add_functions(self, constant_dict, *function_modules, prefix = "calc_"):
        for function_module in function_modules:
            for full_name in dir(function_module):
                if not full_name.startswith(prefix): continue
                fun = getattr(function_module, full_name)
                arity = len(inspect.signature(fun).parameters)
                name = full_name[len(prefix):]
                if name[0].isdigit():
                    signature = []
                    while name[0].isdigit():
                        i = name.find('_')
                        numb = int(name[:i])
                        signature.append(int(name[:i]))
                        name = name[i+1:]
                    assert len(signature) == arity, (name, signature)
                    signature = tuple(signature)
                else:
                    signature = (0,)*arity
                const = constant_dict[name, signature]
                self.set_interpretation(const, fun)

class LogicCalculation:
    def calc_true(self): return True
    def calc_false(self): return False
    def calc_null(self): return None
    def calc__neg(self, x): return not x
    def calc__or(self, x, y): return x or y
    def calc__xor(self, x, y): return bool(x) != bool(y)
    def calc__equiv(self, x, y): return bool(x) == bool(y)
    def calc_to_bool(self, x): return bool(x)
    def calc_to_bool1(self, x): return x is None or x
    def calc__if(self, c, a, b):
        if c: return a
        else: return b
    def calc__require(self, c, a):
        if c: return a
        else: return None
    def calc__try(self, a, b):
        if a is not None: return a
        else: return b
    def calc__is_bool(self, x): return isinstance(x, bool)
    # insane objects except null are not expected to be representable
    def calc__is_sane(self, x): return x is not None

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

