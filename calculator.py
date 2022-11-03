from term import TermFunction, Term
from logic_core import Verifier
from share_term import term_to_instr_list

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
    def __str__(self):
        return self.to_str(str)

class Calculator(Verifier):
    def __init__(self, core):
        super().__init__(core, "calculator")
        self._const_to_term = dict()
        self._interpretation = {
            core.implication : (lambda x,y: not x or y),
            core.equality : (lambda x,y: x == y),
        }
        self._accepted_types = [bool, type(None)]

    def set_interpretation(self, termfun, python_fun):
        if self.core._strict_mode:
            raise Exception("Cannot set function interpretations in strict mode")
        assert isinstance(termfun, TermFunction) and not termfun.is_free_variable
        self._interpretation[termfun] = python_fun
        if termfun.arity == 0:
            self._const_to_term[python_fun()] = termfun.to_term()            

    def accept_type(self, t):
        if self.core._strict_mode:
            raise Exception("Cannot add accepted calculation types in strict mode")
        if t not in self._accepted_types:
            self._accepted_types.append(t)

    def is_admissible_value(self, value):
        if not isinstance(value, self.accepted_types): return False
        if isinstance(value, Container):
            return value.has_admissible_items(self)
        else: return True

    def get_value_name(self, value):
        term = self._const_to_term.get(value, None)
        if term is not None: return str(term)
        elif isinstance(value, Container):
            return container.to_str(self.get_value_name)
        else:
            return str(value)

    def get_value_term(self, value):
        if value in self._const_to_term:
            return self._const_to_term[value]
        assert self.is_admissible_value(value)
        f = TermFunction((), False, self.get_value_name(value))
        term = v.to_term()
        self._interpretation[f] = lambda : value
        self._const_to_term[value] = term
        return term

    def calculate(self, term, only_try = False):
        instr_list, terms = term_to_instr_list(term)
        values = []
        for f_args in instr_list:
            if isinstance(f_args[0], int):
                if only_try: return None
                raise Exception(f"Cannot calculate bound variables in '{term}'")
            if f_args[0].is_free_variable:
                if only_try: return None
                raise Exception(f"Cannot calculate variable '{f_args[0]}' (in '{term}')")
            f = self._interpretation.get(f_args[0], None)
            if f is None:
                if only_try: return None
                raise Exception(f"Calculator: constant '{f_args[0]}' doesn't have an interpretation")
            args = [values[i] for i in f_args[1:]]
            try:
                val = f(*args)
            except AssertionError:
                if only_try: return None
                else: raise
            values.append(val)

        res = self.get_value_term(values[-1])
        calc_term = Term(self.core.equality, (term, res))
        origin = "calculation", term.f
        return self._make_thm(dict(), calc_term, origin)

    def add_logic_functions(self, constants):
        self.set_interpretation(
            constants['true',()],
            lambda: True
        )
        self.set_interpretation(
            constants['false',()],
            lambda: False
        )
        self.set_interpretation(
            constants['null',()],
            lambda: None
        )
        self.set_interpretation(
            constants['_neg',(0,)],
            lambda x: not x
        )
        self.set_interpretation(
            constants['_or',(0,0)],
            lambda x,y: x or y
        )
        self.set_interpretation(
            constants['_and',(0,0)],
            lambda x,y: x and y
        )
        self.set_interpretation(
            constants['_xor',(0,0)],
            lambda x,y: bool(x) != bool(y)
        )
        self.set_interpretation(
            constants['_equiv',(0,0)],
            lambda x,y: bool(x) == bool(y)
        )
        self.set_interpretation(
            constants['to_bool',(0,)],
            lambda x: bool(x)
        )
        self.set_interpretation(
            constants['to_bool1',(0,)],
            lambda x: x is None or bool(x)
        )
        self.set_interpretation(
            constants['_if',(0,0,0)],
            lambda c,a,b: (a if c else b)
        )
        self.set_interpretation(
            constants['_require',(0,0)],
            lambda c,a: (a if c else None)
        )
        self.set_interpretation(
            constants['_try',(0,0)],
            lambda a,b: (a if a is not None else b)
        )
        self.set_interpretation(
            constants['_is_bool',(0,)],
            lambda x: isinstance(x, bool)
        )
        self.set_interpretation( # insane objects are not expected to be representable
            constants['_is_sane',(0,)],
            lambda x: x is not None
        )

if __name__ == "__main__":
    from parse_term import TermParser
    from logic_core import LogicCore
    core = LogicCore()
    parser = TermParser(core)
    parser.parse_file("axioms_logic")
    parser.parse_file("axioms_set")
    parser.parse_file("axioms_fun")
    calculator = Calculator(core)
    calculator.add_logic_functions(parser.name_signature_to_const)
    def tt(s):
        return parser.parse_str(s)
    print(calculator.calculate(tt("to_bool(null)")))

