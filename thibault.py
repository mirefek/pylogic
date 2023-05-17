from term import Term, BVar, TermApp, TermFunction
from parse_term import TermParser
from logic_core import LogicCore
from calculator import Calculator, LogicCalculation
from calc_set_fun import SetCalculation, FunCalculation, BinderCalculation, MathSet, MathFun, MathNumber
from calc_numbers import CalculationNumbers
from calc_thibault import CalculationThibault
from logic_env import LogicEnv, ConstantSet
from int_hammer import IntHammer
from unification import Unification
from pytheorem import Theorem
from rewriter import RootRewriter, RootRewriterSingle, RootRewriterList, RootRewriterCalc
from share_term import TermCache

class ThibaultEnv:
    def __init__(self):
        self.env = LogicEnv()
        self.core = self.env.core
        self.calculator = Calculator(self.core)
        self.calculator.accept_types(MathSet, MathFun, MathNumber)
        self.parser = self.env.parser
        self.parser.int_to_term = lambda n: self.calculator.get_value_term(MathNumber(n))
        self.parser.parse_file("axioms_numbers")
        self.parser.parse_file("axioms_thibault")
        self.env.constants = ConstantSet(self.env) # reload constants
        self.int_hammer = IntHammer(self.core, self.parser.name_signature_to_const, self.calculator)
        self.env.add_generalize_axioms()

        self.calculator.add_functions(
            self.parser.name_signature_to_const,
            LogicCalculation(),
            SetCalculation(),
            FunCalculation(),
            BinderCalculation(),
            CalculationNumbers(),
            CalculationThibault(),
        )

        self.c_zero = self.parser.int_to_term(0)
        self.c_one = self.parser.int_to_term(1)
        self.c_two = self.parser.int_to_term(2)
        self.c_cond = self.parser.name_signature_to_const["cond", (0,0,0)]
        self.c_loop = self.parser.name_signature_to_const["loop", (0,0,2)]
        self.c_compr = self.parser.name_signature_to_const["compr", (0,1)]
        self.c_loop2 = self.parser.name_signature_to_const["loop2", (0,0,0,3,3)]
        self._letter_to_const = {
            'A': self.c_zero,
            'B': self.c_one,
            'C': self.c_two,
            'D': self.parser.name_signature_to_const["_plus", (0,0)],
            'E': self.parser.name_signature_to_const["_minus", (0,0)],
            'F': self.parser.name_signature_to_const["_times", (0,0)],
            'G': self.parser.name_signature_to_const["_floordiv", (0,0)],
            'H': self.parser.name_signature_to_const["_mod", (0,0)],
            'I': self.c_cond,
            'J': self.c_loop,
            'K': BVar(2),
            'L': BVar(1),
            'M': self.c_compr,
            'N': self.c_loop2,
        }
        self._const_to_build_term = {
            self.c_loop: lambda const, args, bound_names: TermApp(
                const, [args[1], args[2], args[0]],
                bound_names = bound_names,
            ),
            self.c_compr: lambda const, args, bound_names: TermApp(
                const, [
                    args[1],
                    args[0].substitute_bvars([BVar(1), self.c_zero]),
                ],
                bound_names = bound_names,
            ),
            self.c_loop2: lambda const, args, bound_names: TermApp(
                const, [
                    args[2], args[3], args[4],
                    args[0].substitute_bvars([BVar(3), BVar(2)]),
                    args[1].substitute_bvars([BVar(3), BVar(2)]),
                ],
                bound_names = bound_names,
            ),
        }
        self.X = self.parser.get_var('X', 0)

    def letters_to_seq_program(self, letters):
        stack = []
        for letter in letters:
            const = self._letter_to_const[letter]
            if isinstance(const, Term): stack.append(const)
            else:
                assert isinstance(const, TermFunction)
                if len(stack) < const.arity: return None
                args = stack[len(stack) - const.arity:]
                # if const.name == "loop2":
                #     args = [arg.substitute_bvars([BVar(3), BVar(2)]) for arg in args[:2]]+args[2:]
                del stack[len(stack) - const.arity:]
                build_term = self._const_to_build_term.get(const, TermApp)
                # build_term = TermApp
                bound_names = (('a',)*n for n in const.signature)
                stack.append(build_term(const, args, bound_names))
        if len(stack) != 1: return None
        [res] = stack
        return res.substitute_bvars([self.X.to_term(), self.c_zero])

    def eval_program(self, prog, x):
        calc_eq = self.calculator.calculate(prog.substitute_free({
            self.X : self.parser.int_to_term(x)
        }), only_try = False)
        if calc_eq is None: return None
        res = self.calculator._interpretation[calc_eq.term.args[1].f]()
        if not isinstance(res, MathNumber) or res.x % 1 != 0: return None
        return res.x

class PushNumbersLeft(RootRewriter):
    def __init__(self, env, calculator):
        axioms = [
            env.axioms.plus_comm,
            env.axioms.times_comm,
            env.constants._minus.def_thm.rw(env.axioms.plus_comm)
        ]
        self.calculator = calculator
        self.root_rewriter_calc = RootRewriterCalc(env, calculator)
        self.comm_rewriter = RootRewriterList([
            RootRewriterSingle(axiom)
            for axiom in axioms
        ]).to_pattern_rw()

    def try_rw(self, term):
        calc_eq = self.root_rewriter_calc.try_rw(term)
        if calc_eq is not None: return calc_eq
        if not term.is_const: return None
        if len(term.args) != 2 or not self.is_number(term[1]): return None
        return self.comm_rewriter.try_rw(term)

    def is_number(self, term):
        if not term.is_const: return False
        if term.f.arity > 0: return False
        value = self.calculator.get_term_value(term)
        return isinstance(value, MathNumber)

class RootRewriterTripack(RootRewriter):
    def __init__(self, tenv):
        self.env = tenv.env
        self.axioms = [
            tenv.env.axioms.loop_to_tri_unpack0,
            tenv.env.axioms.loop_to_tri_unpack1,
        ]
        self.match_terms = [axiom.term[1][0] for axiom in self.axioms]
        self.int_hammer = tenv.int_hammer
        self.P = self.env.parser.get_var('P', 0)
        self.N = self.env.parser.get_var('n', 0)
        self.hammer_cache = dict()
        self.term_cache = TermCache()

    def try_rw(self, term):
        for axiom, match_term in zip(self.axioms, self.match_terms):
            match_term = axiom.term[1][0]
            unification = Unification((set(), None))
            unification.add_requirement(match_term,0, term,1)
            if unification.run(): break
        else: return None

        subst,_ = unification.export_substitutions(
            [match_term.free_vars, term.free_vars],
        )
        if not (subst[self.P].is_free_var and subst[self.P].f.arity == 0): return None
        axiom = axiom.specialize(subst)
        assumption = axiom.term[0]

        if len(assumption.free_vars) != 1: return None
        ori_var = subst[self.P]
        assumption = assumption.substitute_free({ori_var.f : self.P.to_term()})
        assumption = self.term_cache.share(assumption)
        if assumption in self.hammer_cache:
            assumption_thm = self.hammer_cache[assumption]
            if assumption_thm is None: return None
        else:
            assumption_bare = assumption[0].substitute_bvars([self.N.to_term()]) # remove forall
            assumption_bare = assumption_bare[1][1] # remove typing assumptions
            hammer_response = self.int_hammer.verify(assumption_bare, time_limit = 2, debug = False)
            if hammer_response is None:
                self.hammer_cache.get[assumption] = False
            assumption_thm = Theorem(self.env, hammer_response)
            assumption_thm = assumption_thm.generalize(self.N)
            self.hammer_cache[assumption] = assumption_thm

        return axiom.modus_ponens_basic(assumption_thm.specialize({self.P : ori_var}))

if __name__ == "__main__":
    import sys

    tenv = ThibaultEnv()
    env = tenv.env

    ax = env.axioms
    env.add_generalize_axioms()
    rewriter = env.rewriter
    rewriter.add_extensionality(ax.ext_2_loop)
    rewriter.add_extensionality(ax.ext_3_loop2)
    rewriter.add_extensionality(ax.ext_4_loop2)
    rewriter.add_extensionality(ax.ext_1_compr)
    rewriter.add_extensionality(env.add_axiom("forall(x : BODY(x) = BODY2(x)) => let(A, x:BODY(x)) = let(A, x:BODY2(x))"))
    rewriter.add_extensionality(env.add_axiom("forall(x : BODY(x) = BODY2(x)) => sum(A, x:BODY(x)) = sum(A, x:BODY2(x))"))
    rewriter.add_extensionality(env.add_axiom("forall(x : BODY(x) = BODY2(x)) => prod(A, x:BODY(x)) = prod(A, x:BODY2(x))"))

    simp_axioms = []
    simp_axioms.append(ax.simp_zero_minus)
    simp_axioms.append(ax.plus_assoc)
    simp_axioms.append(ax.times_assoc)
    simp_axioms.append(ax.plus_to_double)

    for name in ax._core_dict.keys():
        axiom = getattr(ax, name)
        if name.startswith("cheat_simp_"):
            simp_axioms.append(axiom)

    root_rewriter_tripack = RootRewriterTripack(tenv)
    push_numbers_left = PushNumbersLeft(env, tenv.calculator)
    simp_rewriter = RootRewriterList([
        rewriter.to_root_rewriter(*simp_axioms).to_pattern_rw(),
        push_numbers_left,
        root_rewriter_tripack,
    ])

    for line in sys.stdin:
        print()
        print("Line:", line, end = '')
        prog = tenv.letters_to_seq_program(line.split())
        if prog is None:
            print("Conversion to a program failed")
            continue
        print("Original program:", prog)
        print([tenv.eval_program(prog, n) for n in range(20)])

        print("rewriting...")
        prog = rewriter.run(prog, simp_rewriter, repeat = True).term[1]

        print("Rewritten program:", prog)
        print([tenv.eval_program(prog, n) for n in range(20)])

    print()
