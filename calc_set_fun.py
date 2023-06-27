
import itertools
from calculator import ContainerValue
from fractions import Fraction

class MathNumber:
    def __init__(self, x):
        assert isinstance(x, (int, Fraction))
        self.x = x
    def __hash__(self):
        return hash(self.x)
    def __bool__(self):
        return bool(self.x)
    def __eq__(self, other):
        return isinstance(other, MathNumber) and other.x == self.x
    def __str__(self):
        if self.x % 1 == 0:
            return str(int(self.x))
        else: return str(self.x)

class MathSet(ContainerValue):
    def __init__(self, elements):
        super().__init__()
        self.elements = frozenset(elements)
        if None in self.elements:
            self.elements = self.elements.difference([None])
    def __hash__(self):
        return hash(self.elements)
    def __eq__(self, other):
        return isinstance(other, MathSet) and self.elements == other.elements
    def __len__(self):
        return len(self.elements)

    def get_all_items(self):
        return self.elements
    def to_str(self, item_to_str):
        item_names = [item_to_str(x) for x in self.elements]
        item_names.sort()
        if not item_names: return '{}'
        return "{ " + ', '.join(item_names) + " }"        

class MathFun(ContainerValue):
    def __init__(self, key_value_pairs):
        super().__init__()
        self.mapping = {
            key : value
            for key, value in key_value_pairs
            if key is not None and value is not None
        }
        self.identifier = frozenset(self.mapping.items())
    def __hash__(self):
        return hash(self.identifier)
    def __eq__(self, other):
        return isinstance(other, MathSet) and self.identifier == other.identifier
    def __len__(self):
        return len(self.mapping)

    def get_all_items(self):
        yield from self.mapping.keys()
        yield from self.mapping.values()
    def to_str(self, item_to_str):
        if self.is_seq():
            item_names = [
                item_to_str(self.mapping[MathNumber(i)])
                for i in range(len(self.mapping))
            ]
            if not item_names: return '[]'
            else: return '[ ' + ', '.join(item_names) + ' ]'
        else:
            item_names = [
                item_to_str(x)+" |-> "+item_to_str(y)
                for x,y in self.mapping.items()
            ]
            item_names.sort()
            if not item_names: return 'empty_fun'
            else: return "( " + '; '.join(item_names) + " )"
    def is_seq(self):
        return set(self.mapping.keys()) == set(map(MathNumber, range(len(self.mapping))))

class SetCalculation:
    def calc__is_Set(self, x): return isinstance(x, MathSet)
    def calc__in(self, x, y): return isinstance(y, MathSet) and x in y.elements
    def calc_bools(self): return MathSet([False, True])
    def calc__subset_eq(self, A, B):
        if not isinstance(A, MathSet): return False
        if not isinstance(B, MathSet): return False
        return A.elements <= B.elements
    def calc__supset_eq(self, A, B):
        if not isinstance(A, MathSet): return False
        if not isinstance(B, MathSet): return False
        return A.elements >= B.elements
    def calc__subset(self, A, B):
        if not isinstance(A, MathSet): return False
        if not isinstance(B, MathSet): return False
        return A.elements < B.elements
    def calc__supset(self, A, B):
        if not isinstance(A, MathSet): return False
        if not isinstance(B, MathSet): return False
        return A.elements > B.elements
    def calc__union(self, A, B):
        if not isinstance(A, MathSet): return None
        if not isinstance(B, MathSet): return None
        return MathSet(A.elements | B.elements)
    def calc__intersect(self, A, B):
        if not isinstance(A, MathSet): return None
        if not isinstance(B, MathSet): return None
        return MathSet(A.elements & B.elements)
    def calc__setdiff(self, A, B):
        if not isinstance(A, MathSet): return None
        if not isinstance(B, MathSet): return None
        return MathSet(A.elements - B.elements)
    def calc_Union(self, A):
        if not isinstance(A, MathSet): return None
        res = set()
        for x in A.elements:
            if isinstance(x, MathSet):
                res.update(x.elements)
        return MathSet(res)
    def calc_Intersect(self, A):
        if not isinstance(A, MathSet): return None
        assert len(A.elements) > 0, "cannot calculate the universe"
        res = None
        for x in A.elements:
            if not isinstance(x, MathSet): res = set()
            elif res is None: res = set(x.elements)
            else: res &= x.elements
        return MathSet(res)
    def calc_powerset(self, A):
        if not isinstance(A, MathSet): return None
        elements = list(A.elements)
        res = []
        for mask in itertools.product(*[[False,True]]*len(elements)):
            res.append(MathSet([el for el,taken in zip(elements, mask) if taken]))
        return MathSet(res)
    def calc_unique_el(self, A):
        if not isinstance(A, MathSet): return None
        if len(A.elements) != 1: return None
        return next(iter(A.elements))
    def calc_set_singleton(self, x):
        if x is None: return None
        return MathSet([x])
    def calc_set_pair(self, x,y):
        if x is None: return None
        if y is None: return None
        return MathSet([x,y])
    def calc__empty_set(self):
        return MathSet([])
    
class FunCalculation:
    def calc__is_Fun(self, x):
        return isinstance(x, MathFun)
    def calc__apply(self, f, x):
        if not isinstance(f, MathFun): return None
        return f.mapping.get(x, None)
    def calc_req_sane(self, x): return x
    def calc_domain(self, f):
        if not isinstance(f, MathFun): return None
        return MathSet(f.mapping.keys())
    def calc_image(self, f):
        if not isinstance(f, MathFun): return None
        return MathSet(f.mapping.values())
    def calc_map_set(self, f,A):
        if not isinstance(f, MathFun): return None
        if not isinstance(A, MathSet): return None
        return MathSet([f.mapping.get(x, None) for x in A.elements])
    def calc_empty_fun(self):
        return MathFun([])
    def calc_fun_pair(self, x,y):
        if x is None or y is None: return None
        return MathFun([(x,y)])
    def calc_update(self, f,g):
        if not isinstance(f, MathFun): return None
        if not isinstance(g, MathFun): return None
        res = dict(f.mapping)
        res.update(g.mapping)
        return MathFun(res.items())
    def calc__is_injective(self,f):
        if not isinstance(f, MathFun): return False
        return len(set(f.mapping.values())) == len(f.mapping)
    def calc_inverse(self,f):
        if not isinstance(f, MathFun): return None
        res = dict()
        for x,y in f.mapping.items():
            if y in res: res[y] = None
            else: res[y] = x
        return MathFun(res.items())

class BinderCalculation:
    def calc_0_1_let(self, x, body):
        return body(x)
    def calc_1_0_map_set(self, f_body, A):
        if not isinstance(A, MathSet): return None
        return MathSet([f_body(x) for x in A.elements])
    def calc_0_1_exists_in(self, A, pred):
        if not isinstance(A, MathSet): return False
        return any(pred(x) for x in A.elements)
    def calc_0_1_forall_in(self, A, pred):
        if not isinstance(A, MathSet): return False
        return all(pred(x) for x in A.elements)
    def calc_0_1_exists_uq_in(self, A, pred):
        if not isinstance(A, MathSet): return False
        count = 0
        for x in A.elements:
            if pred(x):
                count += 1
                if count > 1: return False
        return count == 1
    def calc_0_1_unique_in(self, A, pred):
        if not isinstance(A, MathSet): return None
        res = None
        for x in A.elements:
            if pred(x):
                if res is not None: return None
                else: res = x
        return res
    def calc_0_1_take_in(self, A, body):
        if not isinstance(self, A, MathSet): return None
        res = None
        for x in A.elements:
            y = body(x)
            if y in (None, res): continue
            if res is not None: return None
            res = y
    def calc_0_1_select_subset(self, A, pred):
        if not isinstance(A, MathSet): return None
        return MathSet([x for x in A.elements if pred(x)])
    def calc_0_1_fun_on(self, A, body):
        if not isinstance(A, MathSet): return None
        return MathFun([(x,body(x)) for x in A.elements])

if __name__ == "__main__":
    from parse_term import TermParser
    from logic_core import LogicCore
    from calculator import Calculator, LogicCalculation
    core = LogicCore()
    parser = TermParser(core)
    parser.parse_file("axioms_logic")
    parser.parse_file("axioms_set")
    parser.parse_file("axioms_fun")
    calculator = Calculator(core)
    calculator.accept_types(MathSet, MathFun)
    calculator.add_functions(
        parser.name_signature_to_const,
        LogicCalculation(),
        SetCalculation(),
        FunCalculation(),
        BinderCalculation(),
    )
    def tt(s):
        return parser.parse_str(s)
    print(calculator.calculate(tt("powerset(bools | set_singleton({}))")))
    print(calculator.calculate(tt("inverse(update(fun_pair({}, true), fun_pair(true, false)))")))
    print(calculator.calculate(tt("fun_on(bools, x:x)")))

    print(calculator.calculate(tt("""
let(
  update(fun_pair({}, true), fun_pair(true, false)), f :
  fun_on(image(f), y : unique_in(domain(f), x : f[x] = y))
)
""")))
