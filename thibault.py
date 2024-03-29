from term import Term, BVar, TermApp, TermFunction, TermVariable
from parse_term import TermParser
from logic_core import LogicCore, CoreTheorem
from calculator import Calculator, LogicCalculation, CalcTerm
from calc_set_fun import SetCalculation, FunCalculation, BinderCalculation, MathFun, MathNumber
from calc_numbers import CalculationNumbers
from calc_thibault import CalculationThibault
from logic_env import LogicEnv, ConstantSet
from int_hammer import IntHammerCVC4
from unification import Unification
from pytheorem import Theorem
from rewriter import RootRewriter, RootRewriterSingle, RootRewriterList, RootRewriterCalc
from share_term import TermCache
from annotated_term import AnnotatedTerm

class ThibaultEnv:
    def __init__(self):
        self.env = LogicEnv()
        self.core = self.env.core
        self.calculator = self.env.calculator
        self.parser = self.env.parser
        self.parser.parse_file("axioms_thibault")
        self.env.constants = ConstantSet(self.env) # reload constants
        self.int_hammer = IntHammerCVC4(self.core, self.parser.name_signature_to_const, self.calculator)
        self.env.add_generalize_axioms()
        self.add_rewriter_extensionality()

        self.calculator.add_functions(
            self.parser.name_signature_to_const,
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
        self.X = self.parser.get_var('x', 0)

    def add_rewriter_extensionality(self):
        rewriter = self.env.rewriter
        ax = self.env.axioms
        rewriter.add_extensionality(ax.ext_2_loop)
        rewriter.add_extensionality(ax.ext_3_loop2)
        rewriter.add_extensionality(ax.ext_4_loop2)
        rewriter.add_extensionality(ax.ext_1_compr)
        rewriter.add_extensionality(ax.ext_1_comprb)
        rewriter.add_extensionality(self.env.add_axiom("forall(x : BODY(x) = BODY2(x)) => let(A, x:BODY(x)) = let(A, x:BODY2(x))"))
        rewriter.add_extensionality(self.env.add_axiom("forall(x : BODY(x) = BODY2(x)) => sum(A, x:BODY(x)) = sum(A, x:BODY2(x))"))
        rewriter.add_extensionality(self.env.add_axiom("forall(x : BODY(x) = BODY2(x)) => prod(A, x:BODY(x)) = prod(A, x:BODY2(x))"))
        rewriter.add_extensionality(self.env.add_axiom("forall(x : BODY(x) = BODY2(x)) => exists_in(A, x:BODY(x)) = exists_in(A, x:BODY2(x))"))

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

    def eval_closed(self, prog_term):
        calc_term = self.env.calculator.build_calc_term(prog_term, cache = dict())
        res = calc_term.evaluate([])
        if not isinstance(res, MathNumber) or res.x % 1 != 0: return None
        return res.x

    def eval_program(self, prog, x):
        return self.eval_closed(
            prog.substitute_free({
                self.X : self.parser.int_to_term(x)
            })
        )

class PushClosedLeft(RootRewriter):
    def __init__(self, env):
        axioms = [
            env.axioms.plus_comm,
            env.axioms.times_comm,
            env.constants._minus.def_thm.rw(env.axioms.plus_comm)
        ]
        self.comm_rewriter = RootRewriterList([
            RootRewriterSingle(axiom)
            for axiom in axioms
        ]).to_pattern_rw()

    def try_rw(self, term):
        if not term.is_const: return None
        if len(term.args) != 2: return None
        a,b = term.args
        if b.free_vars or not a.free_vars: return None
        return self.comm_rewriter.try_rw(term)

class SimplifyLet(RootRewriter):
    def __init__(self, let_const):
        self.let_const = let_const
        self.def_thm = let_const.def_thm
        self.A = self.def_thm.term[0][0].f
        self.BODY = self.def_thm.term[0][1].f
    def try_rw(self, term):
        if term.f != self.let_const: return None
        if self.is_simple_term(term[0]) or self.is_single_occuring_bvar(term[1], 1):
            return self.def_thm.specialize({
                self.A : term[0],
                self.BODY: term[1],
            })

    def is_single_occuring_bvar(self, term, bvar):
        if bvar not in term.bound_vars: return True
        while not isinstance(term, BVar):
            index = None
            for i,arg in enumerate(term.args):
                if bvar in arg.bound_vars:
                    if index is None: index = i
                    else: return False
            assert index is not None
            bvar += term.f.signature[index]
            term = term[index]
        return True

    def is_simple_term(self,term):
        return isinstance(term, BVar) or term.f.arity == 0

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
            if not isinstance(hammer_response, CoreTheorem):
                self.hammer_cache.get[assumption] = False
                return None
            assumption_thm = Theorem(self.env, hammer_response)
            assumption_thm = assumption_thm.generalize(self.N)
            self.hammer_cache[assumption] = assumption_thm

        return axiom.modus_ponens_basic(assumption_thm.specialize({self.P : ori_var}))

class SimpRewriter(RootRewriterList):
    def __init__(self, tenv):
        ax = tenv.env.axioms
        simp_axioms = []
        simp_axioms.append(ax.simp_zero_minus)
        simp_axioms.append(ax.plus_assoc)
        simp_axioms.append(ax.times_assoc)
        simp_axioms.append(ax.plus_to_double)
        simp_axioms.append(ax.times_to_square)
        minus_ax = tenv.env.add_axiom("(-1)*X = -X")
        simp_axioms.append(minus_ax)

        for name in ax._core_dict.keys():
            axiom = getattr(ax, name)
            if name.startswith("cheat_simp_"):
                simp_axioms.append(axiom)

        super().__init__([
            tenv.env.rewriter.to_root_rewriter(*simp_axioms).to_pattern_rw(),
            SimplifyLet(tenv.env.constants.let),
            PushClosedLeft(tenv.env),
            RootRewriterCalc(tenv.env, tenv.env.calculator),
            RootRewriterTripack(tenv),
        ])

if __name__ == "__main__":
    import sys

    tenv = ThibaultEnv()
    env = tenv.env

    rewriter = env.rewriter
    simp_rewriter = SimpRewriter(tenv)

    for line in sys.stdin:
        print()
        print("Line:", line, end = '')
        prog = tenv.letters_to_seq_program(line.split())
        if prog is None:
            print("Conversion to a program failed")
            continue
        prog_aterm = AnnotatedTerm(prog)
        prog_aterm.add_notation()
        prog_aterm.notation.auto_split_lines()

        print("Original program:")
        print(prog_aterm)
        print([tenv.eval_program(prog, n) for n in range(20)])

        print("rewriting...")
        prog = rewriter.run(prog, simp_rewriter, repeat = True).term[1]

        prog_aterm = AnnotatedTerm(prog)
        prog_aterm.add_notation()
        prog_aterm.notation.auto_split_lines()

        print("Rewritten program:")
        print(prog_aterm)
        print([tenv.eval_program(prog, n) for n in range(20)])

    print()
