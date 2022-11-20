from fractions import Fraction
from calc_set_fun import MathSet, MathFun, MathNumber

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
        return MathNumber(int(x.x // 1))
    def calc__floordiv(self, x,y):
        if not isinstance(x, MathNumber): return None
        if not isinstance(y, MathNumber) or y.x == 0: return None
        return MathNumber(x.x // y.x)
    def calc__mod(self, x,y):
        if not isinstance(x, MathNumber): return None
        if not isinstance(y, MathNumber) or y.x == 0: return None
        return MathNumber(x.x % y.x)
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

    def calc_thibault_cond(self, a,b,c):
        if not isinstance(a, MathNumber) or a.x % 1: return None
        if not isinstance(b, MathNumber) or b.x % 1: return None
        if not isinstance(c, MathNumber) or c.x % 1: return None
        if a.x <= 0: return b
        else: return c
    def calc_2_0_0_thibault_loop(self, f,a,b):
        if not isinstance(a, MathNumber) or a.x % 1: return None
        if not isinstance(b, MathNumber) or b.x % 1: return None
        if a.x <= 0: return b
        for i in range(1, 1+int(a.x)):
            b = f(b, MathNumber(i))
            if b is None: return None
        return b
    def calc_2_2_0_0_0_thibault_loop2(self, f,g,a,b,c):
        if not isinstance(a, MathNumber) or a.x % 1: return None
        if not isinstance(b, MathNumber) or b.x % 1: return None
        if not isinstance(c, MathNumber) or c.x % 1: return None
        if a.x <= 0: return b
        for _ in range(int(a.x)):
            b,c = f(b,c), g(b,c)
            if b is None or c is None: return None
        return b
    def calc_2_0_thibault_compr(self, f, a):
        if not isinstance(a, MathNumber) or a.x % 1: return None
        if a.x < 0: return None
        i = a.x
        m = -1
        z = MathNumber(0)
        while i >= 0:
            m += 1
            val = f(m, z)
            if not isinstance(val, MathNumber) or m.x % 1: return None
            if val <= 0: i -= 1
        return m

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
    print(calculator.calculate(tt("fun_on(0..5, n : fun_on(0..n, k:binom(n,k)))")))
    print(calculator.calculate(tt("forall_in(1..10, n : sum(0..n, k:binom(n,k)) = 2^n)")))

    print(calculator.calculate(tt("""
fun_on(0..10, x :
  thibault_loop2(
    x:y: thibault_loop(
      x:y: thibault_loop(
        x:y: (((1 + 2) * (x * y)) // (2 + y)) + x,
	thibault_loop(
	  x:y: x - thibault_cond(y - x, y, 0),
	  2 + (x // (1 + (2 + 2))),
	  x
	),
        thibault_loop2(
	  x:y: x * y,
	  x:y: 1 + y,
	  0 - thibault_loop(
	    x:y: x - thibault_cond(x, 0, 1 + y),
	    2 + (x // (1 + (2 + 2))),
	    x
	  ),
	  1,
	  1 + thibault_loop(
	    x:y: x - thibault_cond(y - x, y, 0),
	    2 + (x // (1 + (2 + 2))),
	    x
	  )
	)
      ) // thibault_loop(
        x:y: x * y,
	0 - thibault_loop(
	  x:y: x - thibault_cond(x, 0, 1 + y),
	  2 + (x // (1 + (2 + 2))),
	  x
	),
	1
      ),
      1,
      y
    ) - x,
    x:y: 1 + y,
    x,
    1,
    1 + (((x * x) + x) // 2)
  )
)
""")))
