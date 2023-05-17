from logic_core import Verifier, CoreTheorem
from term import Term, TermApp, TermVariable, get_unused_name
from calc_set_fun import MathSet, MathFun, MathNumber
import re
import subprocess

def hammer_was_successful(hammer_output):
    proof_found_reports = [
        "# Proof found!",      # E prover
        "% Refutation found.", # Vampire, who is Tanya by the way? :-)
    ]
    return any(x in hammer_output for x in proof_found_reports)

def assumptions_used_by_hammer(hammer_output):
    last_i = 0
    file_thm_name_start = " file("
    file_thm_name_end = "))."
    thm_names = []
    while True:
        i = hammer_output.find(file_thm_name_start, last_i)
        if i < 0: break
        i += len(file_thm_name_start)
        i2 = hammer_output.find(file_thm_name_end, i)
        assert i2 > 0
        last_i = i2+len(file_thm_name_end)
        file_thm_name = hammer_output[i:i2]
        fname, thm_name = file_thm_name.split(',')
        thm_name = thm_name.strip().strip("'")
        thm_names.append(thm_name)
    return thm_names

class IntHammer(Verifier):
    def __init__(self, core, constants, calculator, solver_cmd = None):
        super().__init__(core, "int_hammer")
        if solver_cmd is None:
            self._solver_cmd = [
                "/home/mirek/formal-math/vampire_z3_rel_static_HEAD_6295",
                "--output_axiom_names", "on",
                "--proof", "tptp",
                "-sas", "z3",
            ]
        else:
            self._solver_cmd = solver_cmd

        self.var_name_regex = re.compile("[A-Z][_a-zA-Z0-9]*")
        self.calculator = calculator
        self.connectives = {
            constants["__impl__", (0,0)] : [0, '=>', 1],
            constants["_neg", (0,)] : ['~', 0],
            constants["_and", (0,0)] : [0,'&',1],
            constants["_or", (0,0)] : [0,'|',1],
            constants["_xor", (0,0)] : [0,'|',1],
            constants["_equiv", (0,0)] : [0,'<=>',1],
            constants["true", ()] : ['$true'],
            constants["false", ()] : ['$false'],
        }
        self.c_divs = [
            constants["_floordiv", (0,0)],
            constants["_mod", (0,0)],
        ]
        self.c_in = constants["_in", (0,0)]
        self.t_ints = constants["ints", ()].to_term()
        self.c_eq = core.equality
        self.c_impl = core.implication
        self.predicates = {
            constants["_less_than_equal", (0,0)] : '$lesseq',
            constants["_less_than", (0,0)] : '$less',
            constants["_greater_than_equal", (0,0)] : '$greatereq',
            constants["_greater_than", (0,0)] : '$greater',
        }
        self.operations = {
            constants["_uminus", (0,)] : "$uminus",
            constants["_plus", (0,0)] : "$sum",
            constants["_minus", (0,0)] : "$difference",
            constants["_times", (0,0)] : "$product",
            constants["_floordiv", (0,0)] : "$quotient_f",
            constants["_mod", (0,0)] : "$remainder_f",
        }

    # we assume a formula without quantifiers, without typing conditions
    # typing conditions will be added to the final theorem
    def verify(self, formula, time_limit = None, debug = False):
        vs = formula.get_ordered_free_vars()
        if any(v.arity > 0 for v in vs):
            if debug:
                print("Int hammer failed: some variables have nonzero arity")
                print([v.to_term() for v in vs])

        # choose TPTP names for variables
        used_names = set()
        var_to_name = dict()
        for v in vs:
            name = v.name
            if not self.var_name_regex.fullmatch(name):
                name = name.capitalize()
                if not self.var_name_regex.fullmatch(name):
                    name = "VAR"
            if name in used_names:
                name = get_unused_name(name, used_names)
            used_names.add(name)
            var_to_name[v] = name

        # encode term to a TPTP string
        formula_str = self.formula_to_str(formula, var_to_name, debug)
        if formula_str is None:
            if debug: print("in:", formula)
            print("Conversion to TPTP TFF failed")
            return None

        if not vs: quantified_str = formula_str
        else:
            quantifiers = [var_to_name[v]+":$int" for v in vs]
            quantifiers = ', '.join(quantifiers)
            quantified_str = f"![{quantifiers}] : ({formula_str})"
        tptp_str = f"tff('pylogic_int_hammer_problem', conjecture, {quantified_str})."
        if debug: print("TPTP formula:", tptp_str)

        solver_cmd = self._solver_cmd
        if time_limit is not None:
            assert isinstance(time_limit, int)
            solver_cmd = solver_cmd+['-t', str(time_limit)+'s']
        hammer_output = subprocess.run(
            solver_cmd,
            input = tptp_str.encode(),
            capture_output = True,
        )
        hammer_output = hammer_output.stdout.decode() # get output string

        if not hammer_was_successful(hammer_output):
            if debug:
                if isinstance(debug, int) and debug > 5:
                    print(hammer_output)
                print("External hammer failed!")
                return None

        if debug: print("External hammer succeeded :-)")

        # add typing assumptions
        for v in reversed(vs):
            formula = TermApp(
                self.c_impl, (
                    TermApp(self.c_in, (v.to_term(), self.t_ints)),
                    formula,
                )
            )
        return self._make_thm(dict(), formula)

    def formula_to_str(self, formula, var_to_name, debug):

        connective = self.connectives.get(formula.f, None) # logical connective
        if connective is not None:
            arg_strs = []
            for arg in formula.args:
                arg_str = self.formula_to_str(arg, var_to_name, debug)
                if arg_str is None:
                    if debug: print("in:", arg)
                    return None
                arg_strs.append(arg_str)
            substrs = [x if isinstance(x, str) else arg_strs[x] for x in connective]
            if len(substrs) == 1: return substrs[0]
            return '('+' '.join(substrs)+')'

        predicate = self.predicates.get(formula.f, None) # inequality
        if predicate is not None:
            arg_strs = []
            nnone_conditions = []
            for arg in formula.args:
                arg_str = self.term_to_str(arg, var_to_name, nnone_conditions, debug)
                if arg_str is None:
                    if debug: print("in:", arg)
                    return None
                arg_strs.append(arg_str)
            predicate_str = predicate+'('+', '.join(arg_strs)+')'
            if not nnone_conditions: return predicate_str
            return '('+" & ".join([predicate_str]+nnone_conditions)+')'

        if formula.f == self.c_eq: # equality
            nnone_conditions0 = []
            nnone_conditions1 = []
            arg_strs = []
            for arg, nnone_conditions in zip(formula.args, [nnone_conditions0, nnone_conditions1]):
                arg_str = self.term_to_str(arg, var_to_name, nnone_conditions, debug)
                if arg_str is None:
                    if debug: print("in:", arg)
                    return None
                arg_strs.append(arg_str)
            eq_str = f"({arg_strs[0]} = {arg_strs[1]})"
            if not (nnone_conditions0 or nnone_conditions1): return eq_str
            nnone_str = '('+" & ".join([eq_str]+nnone_conditions0+nnone_conditions1)+')'
            if not (nnone_conditions0 and nnone_conditions1): return nnone_str
            nnone_conditions0 = '('+' & '.join(nnone_conditions0)+')'
            nnone_conditions1 = '('+' & '.join(nnone_conditions1)+')'
            none_str = f"((~nnone_conditions0) & (~nnone_conditions1))"
            return f"(nnone_str | none_str)"

        if debug: print("Unexpected function in boolean mode:", formula.f)
        return None

    def term_to_str(self, term, var_to_name, nnone_conditions, debug):

        var_name = var_to_name.get(term.f)
        if var_name is not None: return var_name
        
        operation = self.operations.get(term.f, None)
        if operation is not None:
            arg_strs = []
            for arg in term.args:
                arg_str = self.term_to_str(arg, var_to_name, nnone_conditions, debug)
                if arg_str is None:
                    if debug: print("in:", arg)
                    return None
                arg_strs.append(arg_str)
            if term.f in self.c_divs:
                nnone_conditions.append(f"({arg_strs[-1]} != 0)")
            return operation+'('+', '.join(arg_strs)+')'

        if term.f.arity == 0: # number
            value = self.calculator.get_term_value(term)
            if isinstance(value, MathNumber) and value.x % 1 == 0:
                return str(int(value.x))

        if debug: print("Unexpected function in term mode:", term.f)
        return None

if __name__ == "__main__":
    from parse_term import TermParser
    from logic_core import LogicCore
    from calculator import Calculator, LogicCalculation

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
    hammer = IntHammer(
        core = core,
        constants = parser.name_signature_to_const,
        calculator = calculator
    )

    problem_str = """
       n >= 0 =>
       x >= (n+1)*n//2 =>
       n <= (10 + (2 * (x // 36)))
    """
    thm = hammer.verify(parser.parse_str(problem_str), debug = True)
    print(thm)
