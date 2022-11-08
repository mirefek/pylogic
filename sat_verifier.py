from term import TermConstant
from logic_core import Verifier
from pysat.solvers import Solver
from share_term import term_to_instr_list

class SatVerifier(Verifier):
    def __init__(self, core):
        super().__init__(core, "sat_verifier")
        self._const_to_clause_gen = {
            core.implication : lambda x,y,res: [(x,res), (-y,res), (-x,y,-res)]
        }

    def set_interpretation(self, termfun, clause_generator):
        if self.core._strict_mode:
            raise Exception("Cannot set sat function interpretations in strict mode")
        assert isinstance(termfun, TermConstant)
        self._const_to_clause_gen[termfun] = clause_generator

    def set_standard_functions(self, constants):
        self.set_interpretation(
            constants['true',()],
            lambda res: [(res,)]
        )
        self.set_interpretation(
            constants['false',()],
            lambda res: [(-res,)]
        )
        self.set_interpretation(
            constants['_neg',(0,)],
            lambda x,res: [(x,res),(-x,-res,)]
        )
        self.set_interpretation(
            constants['_or',(0,0)],
            lambda x,y,res: [(-x,res), (-y,res), (x,y,-res)]
        )
        self.set_interpretation(
            constants['_and',(0,0)],
            lambda x,y,res: [(-x,-y,res), (x,-res), (y,-res)]
        )
        self.set_interpretation(
            constants['_xor',(0,0)],
            lambda x,y,res: [(-x,y,res), (x,-y,res), (-x,-y,-res), (x,y,-res)]
        )
        self.set_interpretation(
            constants['_equiv',(0,0)],
            lambda x,y,res: [(-x,-y,res), (x,y,res), (-x,y,-res), (x,-y,-res)]
        )
        self.set_interpretation(
            constants['to_bool',(0,)],
            lambda x,res: [(-x,res), (x,-res)]
        )

    def verify(self, term, only_try = False):
        instr_list, terms = term_to_instr_list(term)
        bool_nodes = [None]*len(instr_list)
        stack = [len(instr_list)-1]
        while stack:
            i = stack.pop()
            if bool_nodes[i]: continue
            bool_nodes[i] = True
            f_args = instr_list[i]
            if f_args[0] in self._const_to_clause_gen:
                stack.extend(f_args[1:])
        last_sv = 0
        with Solver() as solver:
            for i, (is_bool, f_args) in enumerate(zip(bool_nodes, instr_list)):
                if not is_bool: continue
                last_sv += 1
                bool_nodes[i] = last_sv
                f = self._const_to_clause_gen.get(f_args[0], None)
                if f is None: continue
                args = [bool_nodes[j] for j in f_args[1:]] + [last_sv]
                for clause in f(*args):
                    solver.add_clause(clause)
            solver.add_clause((-last_sv,))
            if solver.solve():
                if only_try: return None
                else:
                    sv_to_value = {
                        abs(x) : x > 0
                        for x in solver.get_model()
                    }
                    for bool_node, t in zip(bool_nodes, terms):
                        if bool_node is None: return
                        value = sv_to_value[bool_node]
                        print(int(value), ':', t)
                    raise Exception("SAT checked term is not generally propositionally true")
            else: # no counterexample -> theorem
                return self._make_thm(dict(), term)

if __name__ == "__main__":
    from parse_term import TermParser
    from logic_core import LogicCore
    core = LogicCore()
    parser = TermParser(core)
    parser.parse_file("axioms_logic")
    parser.parse_file("axioms_set")
    parser.parse_file("axioms_fun")
    verifier = SatVerifier(core)
    verifier.set_standard_functions(parser.name_signature_to_const)
    def tt(s):
        return parser.parse_str(s)
    print(verifier.verify(tt("!A => (A => B)")))
    print(verifier.verify(tt("B => (A => B)")))
    print(verifier.verify(tt("A => !B => !(A => B)")))
    print(verifier.verify(tt("A => (B => C) => (A => C) => (B => C)")))
    print(verifier.verify(tt("((A => B) => A) => A")))
    print(verifier.verify(tt("(A && B) => A")))
    print(verifier.verify(tt("(A && B) => B")))
    print(verifier.verify(tt("A => B => (A && B)")))
    print(verifier.verify(tt("A => (A || B)")))
    print(verifier.verify(tt("B => (A || B)")))
    print(verifier.verify(tt("(A => C) => (B => C) => ((A || B) => C)")))
    print(verifier.verify(tt("(A && B) && C <=> A && (B && C)")))
    print(verifier.verify(tt("(A || B) && C <=> (A && C) || (B && C)")))
    print(verifier.verify(tt("A ^^ true <=> !A")))
    print(verifier.verify(tt("A ^^ false <=> A")))
    print(verifier.verify(tt("true ^^ A <=> !A")))
    print(verifier.verify(tt("false ^^ A <=> A")))
    print(verifier.verify(tt("(A ^^ B) ^^ C <=> A ^^ (B ^^ C)")))
    print(verifier.verify(tt("to_bool(A) <=> A")))
