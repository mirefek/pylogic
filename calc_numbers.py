from fractions import Fraction
from calc_set_fun import MathSet, MathFun

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
        if self.x % 1 == 0: return str(int(self.x))
        else: return str(self.x)

class CalculationNumbers:
    def calc__plus(self, x,y):
        if not isinstance(x, MathNumber): return None
        if not isinstance(y, MathNumber): return None
        return MathNumber(x.x + y.x)
    def calc__uminus(self, x):
        if not isinstance(x, MathNumber): return None
        return MathNumber(-x.x)
    def calc__minus(self, x,y):
        if not isinstance(x, MathNumber): return None
        if not isinstance(y, MathNumber): return None
        return MathNumber(x.x - y.x)
    def calc__times(self, x,y):
        if not isinstance(x, MathNumber): return None
        if not isinstance(y, MathNumber): return None
        return MathNumber(x.x * y.x)
    def calc_udivide(self, x):
        if not isinstance(x, MathNumber) or x.x == 0: return None
        return MathNumber(1 / Fraction(x.x))
    def calc__divide(self, x,y):
        if not isinstance(x, MathNumber): return None
        if not isinstance(y, MathNumber) or y.x == 0: return None
        return MathNumber(Fraction(x.x) / y.x)

    def calc__less_than_equal(self, x,y):
        if not isinstance(x, MathNumber): return False
        if not isinstance(y, MathNumber): return False
        return x.x <= y.x
    def calc__less_than(self, x,y):
        if not isinstance(x, MathNumber): return False
        if not isinstance(y, MathNumber): return False
        return x.x < y.x
    def calc__greater_than_equal(self, x,y):
        if not isinstance(x, MathNumber): return False
        if not isinstance(y, MathNumber): return False
        return x.x >= y.x
    def calc__greater_than(self, x,y):
        if not isinstance(x, MathNumber): return False
        if not isinstance(y, MathNumber): return False
        return x.x > y.x

    def calc__int_range(self, x,y):
        if not isinstance(x, MathNumber) or x.x % 1: return None
        if not isinstance(y, MathNumber) or y.x % 1: return None
        return MathSet(map(MathNumber, range(int(x.x), int(y.x)+1)))
    def calc_maximum(self, A):
        if not isinstance(A, MathSet): return None
        if any(
            not isinstance(x, MathNumber)
            for x in A.elements
        ): return None
        return max(A.elements, key = lambda x : x.x)
    def calc_minimum(self, A):
        if not isinstance(A, MathSet): return None
        if any(
            not isinstance(x, MathNumber)
            for x in A.elements
        ): return None
        return min(A.elements, key = lambda x : x.x)
    def calc_supremum(self, A):
        return self.calc_maximum(A)
    def calc_infimum(self, A):
        return self.calc_minimum(A)
    def calc_floor(self, x):
        if not isinstance(x, MathNumber): return None
        return x.x // 1
    def calc__floordiv(self, x,y):
        if not isinstance(x, MathNumber): return None
        if not isinstance(y, MathNumber) or y.x == 0: return None
        return x.x // y.x
    def calc__mod(self, x,y):
        if not isinstance(x, MathNumber): return None
        if not isinstance(y, MathNumber) or y.x == 0: return None
        return x.x % y.x
    def calc_divides(self, x,y):
        if not isinstance(x, MathNumber): return False
        if not isinstance(y, MathNumber) or y.x == 0: return False
        return x.x % y.x == 0

    def calc_0_1_sum(self, A, body):
        if not isinstance(A, MathSet): return None
        res = 0
        for x in A.elements:
            y = body(x)
            if not isinstance(y, MathNumber): return None
            res += y.x
        return MathNumber(res)
    def calc_0_1_prod(self, A, body):
        if not isinstance(A, MathSet): return None
        res = 1
        for x in A.elements:
            y = body(x)
            if not isinstance(y, MathNumber): return None
            res *= y.x
        return MathNumber(res)

    def calc_factorial(self, n):
        if not isinstance(n, MathNumber) or n.x % 1 or n.x < 0: return None
        res = 1
        for x in range(1, int(n.x)+1): res *= x
        return MathNumber(res)
    def calc_binom(self, n, k):
        if not isinstance(n, MathNumber) or n.x % 1 or n.x < 0: return None
        if not isinstance(k, MathNumber) or k.x % 1: return None
        n = int(n.x)
        k = int(k.x)
        if k < 0 or k > n: return 0
        if n-k < k: k = n-k
        res = 1
        for i in range(k):
            res = res * (n-i) // (i+1)
        return MathNumber(res)
    def calc__power(self, x, n):
        if not isinstance(x, MathNumber) or x.x % 1: return None
        if not isinstance(n, MathNumber) or n.x % 1 or n.x < 0: return None
        return MathNumber(x.x ** n.x)

if __name__ == "__main__":
    from parse_term import TermParser
    from logic_core import LogicCore
    from calculator import Calculator, LogicCalculation
    from calc_set_fun import SetCalculation, FunCalculation, BinderCalculation
    core = LogicCore()
    calculator = Calculator(core)
    calculator.accept_types(MathSet, MathFun, MathNumber)
    parser = TermParser(
        core,
        int_to_term = lambda n: calculator.get_value_term(MathNumber(n))
    )
    parser.parse_file("axioms_logic")
    parser.parse_file("axioms_set")
    parser.parse_file("axioms_fun")
    parser.parse_file("axioms_numbers")
    calculator.add_functions(
        parser.name_signature_to_const,
        LogicCalculation(),
        SetCalculation(),
        FunCalculation(),
        BinderCalculation(),
        CalculationNumbers(),
    )
    def tt(s):
        return parser.parse_str(s)
    print(calculator.calculate(tt("sum(1..10, x : x)")))
    print(calculator.calculate(tt("sum(1..5, a:sum(1..a, x : 2*x-1))")))
    print(calculator.calculate(tt("let(5, n : fun_on(0..n, k:binom(n,k)))")))
    print(calculator.calculate(tt("forall_in(1..10, n : sum(0..n, k:binom(n,k)) = 2^n)")))
