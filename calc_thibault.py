from calc_set_fun import MathNumber

class CalculationThibault:

    def calc_cond(self, a,b,c):
        if not isinstance(a, MathNumber) or a.x % 1: return None
        if not isinstance(b, MathNumber) or b.x % 1: return None
        if not isinstance(c, MathNumber) or c.x % 1: return None
        if a.x <= 0: return b
        else: return c
    def calc_0_0_2_loop(self, a,b,f):
        if not isinstance(a, MathNumber) or a.x % 1: return None
        if not isinstance(b, MathNumber) or b.x % 1: return None
        if a.x <= 0: return b
        for i in range(1, 1+int(a.x)):
            b = f(b, MathNumber(i))
            if b is None: return None
        return b
    def calc_0_0_0_3_3_loop2(self, a,b,c,f,g):
        if not isinstance(a, MathNumber) or a.x % 1: return None
        if not isinstance(b, MathNumber) or b.x % 1: return None
        if not isinstance(c, MathNumber) or c.x % 1: return None
        if a.x <= 0: return b
        for i in range(1, 1+int(a.x)):
            b,c = f(b,c,MathNumber(i)), g(b,c,MathNumber(i))
            if b is None or c is None: return None
        return b
    def calc_0_1_compr(self, a, f):
        if not isinstance(a, MathNumber) or a.x % 1: return None
        if a.x < 0: return None
        i = a.x
        m = -1
        while i >= 0:
            m += 1
            val = f(MathNumber(m))
            if not isinstance(val, MathNumber) or val.x % 1: return None
            if val.x <= 0: i -= 1
        return MathNumber(m)

    def calc_tri_pack(self,x,y):
        if not isinstance(x, MathNumber) or x.x % 1 or x.x < 0: return None
        if not isinstance(y, MathNumber) or y.x % 1 or y.x < 0: return None
        n = x.x+y.x
        x = x.x
        return MathNumber(n*(n+1)//2 + x)
    def calc_tri_unpack0(self,p):
        if not isinstance(p, MathNumber) or p.x % 1: return None
        if p.x < 0: return p
        p = p.x
        i = 1
        while p >= i:
            p -= i
            i += 1
        return MathNumber(p)
    def calc_tri_unpack1(self,p):
        if not isinstance(p, MathNumber) or p.x % 1: return None
        if p.x < 0: return MathNumber(-p.x)
        p = p.x
        i = 1
        while p >= i:
            p -= i
            i += 1
        return MathNumber(i-p-1)

if __name__ == "__main__":
    from parse_term import TermParser
    from logic_core import LogicCore
    from calculator import Calculator, LogicCalculation
    from calc_set_fun import SetCalculation, FunCalculation, BinderCalculation, MathSet, MathFun, MathNumber
    from calc_numbers import CalculationNumbers
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
    parser.parse_file("axioms_thibault")
    calculator.add_functions(
        parser.name_signature_to_const,
        LogicCalculation(),
        SetCalculation(),
        FunCalculation(),
        BinderCalculation(),
        CalculationNumbers(),
        CalculationThibault(),
    )
    def tt(s):
        return parser.parse_str(s)

    ZERO = parser.int_to_term(0)
    ONE = parser.int_to_term(1)
    TWO = parser.int_to_term(2)
    plus = parser.name_signature_to_const["_plus", (0,0)]
    fun_on = parser.name_signature_to_const["fun_on", (0,1)]
    loop = parser.name_signature_to_const["loop", (2,0,0)]
    _int_range = parser.name_signature_to_const["_int_range", (0,0)]
    def int_range(a,b):
        return _int_range(parser.int_to_term(a), parser.int_to_term(b))

    print(calculator.calculate(
        fun_on(
            int_range(0,10),
            lambda x : loop(lambda x,y: plus(x,x), x, ONE)
        )
    ))
    
    print(calculator.calculate(tt("""
fun_on(0..10, x :
  loop2(
    x:y: loop(
      x:y: loop(
        x:y: (((1 + 2) * (x * y)) // (2 + y)) + x,
	loop(
	  x:y: x - cond(y - x, y, 0),
	  2 + (x // (1 + (2 + 2))),
	  x
	),
        loop2(
	  x:y: x * y,
	  x:y: 1 + y,
	  0 - loop(
	    x:y: x - cond(x, 0, 1 + y),
	    2 + (x // (1 + (2 + 2))),
	    x
	  ),
	  1,
	  1 + loop(
	    x:y: x - cond(y - x, y, 0),
	    2 + (x // (1 + (2 + 2))),
	    x
	  )
	)
      ) // loop(
        x:y: x * y,
	0 - loop(
	  x:y: x - cond(x, 0, 1 + y),
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

