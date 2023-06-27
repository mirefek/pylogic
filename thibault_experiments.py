primes_str = "B L A L E K K B L K H A B I N A B K L H L N F K D D L K B B K D N B K D G"

from thibault import *
import numpy as np
import itertools
from contextlib import contextmanager

tenv = ThibaultEnv()
env = tenv.env
rewriter = env.rewriter
co = env.constants
simp_rewriter = SimpRewriter(tenv)
parser = env.parser

prog = tenv.letters_to_seq_program(primes_str.split())
def rewrite(*rws, repeat = True):
    global prog
    def process_rw(rw):
        if isinstance(rw, str):
            ax = env.add_axiom(rw)
            assert all(v.arity == 0 or v.name[0].isupper() for v in ax.free_vars), ax.free_vars
            return ax
        else: return rw
    res = rewriter.run(prog, *map(process_rw, rws), repeat = repeat)
    assert res is not None
    prog = res.term[1]

@contextmanager
def local_prog(program):
    if isinstance(program, str):
        program = parser.parse_str(program)
    global prog
    ori = prog
    prog = program
    yield
    prog = ori

def show_program():
    global prog
    print(prog)
    print([tenv.eval_program(prog, n) for n in range(20)])

def eval_closed(self, prog):
    calc_eq = self.calculator.calculate(prog.substitute_free({
        self.X : self.parser.int_to_term(x)
    }), only_try = False)
    if calc_eq is None: return None
    res = self.calculator._interpretation[calc_eq.term.args[1].f]()
    if not isinstance(res, MathNumber) or res.x % 1 != 0: return None
    return res.x

def eval_matrix(program, n = 10):
    vs = program.get_ordered_free_vars()
    res = np.zeros([n]*len(vs), dtype = np.int64)
    for vals in itertools.product(*[range(n)]*len(vs)):
        cur_res = tenv.eval_closed(
            program.substitute_free({
                v : env.parser.int_to_term(val)
                for v,val in zip(vs, vals)
            })
        )
        if cur_res is None: cur_res = -440
        res[vals] = cur_res
    return res

def show_matrix(program, n = 10):
    print(program)
    print("Variables:", *program.get_ordered_free_vars())
    matrix = eval_matrix(program, n)
    print(matrix)

print("Original program:")
show_program()

subprog = parser.parse_str("loop2(1, a % b, b, d : e : f : loop2(d, 1, if e % d <= 0 ; 0 else 1, g : h : i : - h, g : h : i : g), d : e : f : 0)")
show_matrix(subprog)
subprog = parser.parse_str("loop2(d, 1, if e % d <= 0 ; 0 else 1, g : h : i : - h, g : h : i : g)")
show_matrix(subprog)
subprog = parser.parse_str("loop2(d, 1, 0, g : h : i : - h, g : h : i : g)")
show_matrix(subprog)

print("rewriting...")
rewrite(simp_rewriter)

print("Rewritten program:")
show_program()

rewrite("""
loop2(x,y,z, a:b:c:BODY1(b), a:b:c:BODY2(a)) =
  loop(x//2, if x%2 = 0; y else BODY1(z), a:b: BODY1(BODY2(a)))
""")
rewrite("""
loop(x,y, a:b:-a) = y*(-1)^x
""")

show_program()

subprog = parser.parse_str("loop2(1, a % b, b, d : e : f : (if d % 2 = 0 ; 1 else - if e % d <= 0 ; 0 else 1) * (- 1) ^ (d // 2), d : e : f : 0)")
show_matrix(subprog)

rewrite("""
loop2(x,y,z, a:b:c:BODY(a,b,c), a:b:c:T) = loop(x-1, BODY(y,z,1), a:b:BODY(a,T,b+1))
""")
show_program()

rewrite("""
(-1) ^ n = if n%2 = 0; 1 else -1
""")

rewrite(simp_rewriter)
rewrite("""
loop(0,x, a:b:BODY(a,b)) = x
""")

rewrite("""
-(if C; A else B) = if C; -A else -B
""")

rewrite(simp_rewriter)

rewrite("""
(if C; A else B)*X =
if C; A*X else B*X
""", """
X*(if C; A else B) =
if C; X*A else X*B
""")

rewrite(simp_rewriter)

rewrite("""
(if C1; (if C2; A else B) else (if C2; X else Y))
= if C1 && C2; A
else if C1 && !C2; B
else if !C1 && C2; X
else Y
""")

rewrite("(n // 2 % 2 = 0) = (n % 4 < 2)")
rewrite(
    "(n % 4 < 2 && n % 2 = 0) = (n%4 = 0)",
    "(n % 4 < 2 && n % 2 != 0) = (n%4 = 1)",
    "(n % 4 !< 2 && n % 2 = 0) = (n%4 = 2)",
)
rewrite("((a % b) <= 0) = (a % b = 0)")

show_program()

rewrite("""
(if C1; if C2; a else b else if C3; b else c)
= (if !C1 && !C3; c else if C1 && C2; a else b)
""")

rewrite("""
(if x % 4 = 0 ; A else if ! (x % 4 = 1) && ! (x % 4 = 2) ; B else C)
= (if x % 4 = 0 ; A else if (x % 4 = 3) ; B else C)
""")

rewrite("""
(if C1; if C2; a else b else if C3; a else c)
= (if C1 && !C2; b else if !C1 && !C3; c else a)
""")

rewrite("""
(if C1; a else if C2; a else b)
= (if C1 || C2; a else b)
""")

rewrite("(!A && !B) = !(A || B)")
rewrite("(if !C; a else b) = (if C; b else a)")

show_program()

rewrite("""
loop2(I,A,B, a:b:k:BODY(a,b,k), a:b:k:b)
= loop(I,A, a:k:BODY(a,B,k))
""")

rewrite("""
1+a+b = 1+b+a
""", repeat = False)

rewrite("""
(if C1; b else if C2; 0 else -b)
= b*(if C1; 1 else if C2; 0 else -1)
""", repeat = False)

rewrite("""
(if a % (1 + X) % 4 = 0 || (a % (1 + X) % 4 = 3 && ! ((1 + X) % (a % (1 + X)) = 0)) ; 1 else if a % (1 + X) % 4 = 3 || (a % (1 + X) % 4 = 1 && (1 + X) % (a % (1 + X)) = 0) ; 0 else - 1)
 = let(a % (1 + X), b : if b % 4 = 0 || (b % 4 = 3 && ! ((1 + X) % (b) = 0)) ; 1 else if b % 4 = 3 || (b % 4 = 1 && (1 + X) % (b) = 0) ; 0 else - 1)
""")

show_program()

rewrite("""
loop(X, 1, a : k : 1 + a + (1+X) * let(a % (1+X), b : BODY(b))) // (1+X)
= sum(1..X, b : BODY(b))+1
""")

show_program()

rewrite("""
(if X%4 = 0 || (X%4 = 3 && !C); a
 else if X%4 = 3 || (X%4 = 1 && C); b
 else c)
=
(if X%2 = 1 && C; b
 else if (X+1)%4 < 2; a
 else c)
""")

rewrite("""
sum(1 .. X, b : BODY(b)) = sum(1 .. X//2, b : BODY(2*b)) + sum(1 .. (X+1)//2, b : BODY(2*b-1))
""", repeat = False)
rewrite(simp_rewriter)
rewrite("(2*x)%2 = 0", "((1+2*b)%4 < 2) = (b%2 = 0)", "(-1 + 2*b)%2 = 1", "((2*b) % 4 < 2) = (b%2 = 0)")
rewrite(simp_rewriter)
rewrite("(true && X) = X", "(false && X) = false", "(if false; a else b) = b")
rewrite("(if X%2 = 0; 1 else -1) = (-1)^X")

show_program()

rewrite("sum(1 .. X, a : (-1)^a) = (if X%2 = 0; 1 else 0)-1")
rewrite(simp_rewriter)
rewrite("((X // 2) % 2 = 0) = (X % 4 < 2)")

show_program()

rewrite("""
sum(1..n, a : if PRED(a); 0 else BODY(a) ) =
sum(1..n, a : BODY(a) ) +
sum(1..n, a : if PRED(a); -BODY(a) else 0 )
""")
rewrite("sum(1 .. X, a : (-1)^a) = (if X%2 = 0; 1 else 0)-1")
rewrite(simp_rewriter)
rewrite("((X // 2) % 2 = 0) = (X % 4 < 2)")

show_program()

rewrite("sum(A..B, x : BODY(x)) = sum(-1+A..-1+B, x : BODY(1+x))", repeat = False)
rewrite("a*(b+c) = a*b + a*c")
rewrite(simp_rewriter)
rewrite("-(-1)^(1+n) = (-1)^n")
rewrite("a + b//c = (a*c+b)//c")
rewrite(simp_rewriter)

show_program()

rewrite("""sum(S..(-1+X)//2, a:BODY(a)) =
(if X%2 = 0; -BODY(X//2) else 0) +
sum(S..X//2, a:BODY(a))
""")

show_program()

rewrite("- (if C; a else b) = (if C; -a else -b)")
rewrite("2 * (X // 2) = X") # under a context where we know X is even
rewrite("n%n = 0")
rewrite(simp_rewriter)
rewrite("(if true; a else b) = a")
rewrite("(-1) + (if C; a else b) = (if C; a-1 else b-1)")

show_program()

rewrite("""
(if (1+X) % 4 < 2; a else b)
= (if X%4 = 0; a else if X%4 = 1; b else if X%4 = 2; b else a)
""")
rewrite("""
(if X % 4 < 2; a else b)
= (if X%4 = 0; a else if X%4 = 1; a else if X%4 = 2; b else b)
""")
rewrite("""
(if X%2 = 0; a else b)
= (if X%4 = 0; a else if X%4 = 1; b else if X%4 = 2; a else b)
""")
rewrite("""
(if X%4 = 0; -(-1)^(X//2) else b)
= (if X%4 = 0; -1 else b)
""")
rewrite("""
(if X%4 = 2; -(-1)^(X//2) else b)
= (if X%4 = 2; 1 else b)
""")

show_program()

rewrite("(if C; a1 else b1) + (if C; a2 else b2) = (if C; a1+a2 else b1+b2)")
rewrite(simp_rewriter)
rewrite("(if C; a else a) = a")
rewrite(simp_rewriter)


#rewrite("A+B+B = A+2*B", co.let, "A//B//C = A//(B*C)", tenv.calculator)

#rewrite("loop(A,B,x:y:if PRED(x,y); C else x) = if exists_in(1..A, x:PRED(B,x)); C else B", repeat = False)
print("Final program:")
show_program()
