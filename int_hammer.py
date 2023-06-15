from logic_core import Verifier, CoreTheorem
from term import Term, TermApp, TermVariable, get_unused_name
from calc_set_fun import *
from calc_numbers import CalculationNumbers
import re
import subprocess

class AbstractIntHammer(Verifier):
    def __init__(self, core, constants, calculator):
        super().__init__(core, "int_hammer")

        self.calculator = calculator
        self.connectives = {
            core.implication : 'impl',
            constants["_neg", (0,)] : 'neg',
            constants["_and", (0,0)] : 'and',
            constants["_or", (0,0)] : 'or',
            constants["_xor", (0,0)] : 'xor',
            constants["_equiv", (0,0)] : 'equiv',
            constants["true", ()] : 'true',
            constants["false", ()] : 'false',
        }
        self.predicates = {
            core.equality : 'eq',
            constants["_less_than_equal", (0,0)] : 'le',
            constants["_less_than", (0,0)] : 'lt',
            constants["_greater_than_equal", (0,0)] : 'ge',
            constants["_greater_than", (0,0)] : 'gt',
        }
        self.operations = {
            constants["_uminus", (0,)] : 'uminus',
            constants["_plus", (0,0)] : 'plus',
            constants["_minus", (0,0)] : 'minus',
            constants["_times", (0,0)] : 'times',
            constants["_floordiv", (0,0)] : 'div',
            constants["_mod", (0,0)] : 'mod',
            constants["_power", (0,0)] : 'power',
        }

        # for adding typing assumptions
        self.c_in = constants["_in", (0,0)]
        self.t_ints = constants["ints", ()].to_term()
        self.c_impl = core.implication

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
            name = self.get_varname(v.name, used_names)
            used_names.add(name)
            var_to_name[v] = name

        # encode term to a TPTP string
        formula_str = self.formula_to_str(formula, var_to_name, debug)
        if formula_str is None:
            if debug:
                print("in:", formula)
                print("Exporting arithmetical formula failed")
            return None

        if time_limit is not None:
            if isinstance(time_limit, int): time_limit = int(time_limit)
            elif isinstance(time_limit, float): time_limit = float(time_limit)
            else: raise Exception(f"Unexpected type of time_limit = {time_limit} : {type(time_limie)}")
        response = self.verify_str(
            formula_str,
            [var_to_name[v] for v in vs],
            time_limit = time_limit,
            debug = debug,
        )

        if isinstance(response, dict):
            counterexample = {
                v : self.calculator.get_value_term(MathNumber(response[name]))
                for v,name in var_to_name.items()
            }
            if debug:
                print("counterexample found:")
                # print(counterexample)
            return counterexample
        elif response is not True:
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
            return self.connective_to_str(connective, arg_strs)

        predicate = self.predicates.get(formula.f, None) # inequality
        if predicate is not None:
            arg_strs = []
            nnone_conditions = []
            for arg in formula.args:
                nnone_conditions.append([])
                arg_str = self.term_to_str(arg, var_to_name, nnone_conditions[-1], debug)
                if arg_str is None:
                    if debug: print("in:", arg)
                    return None
                arg_strs.append(arg_str)
            predicate_str = self.predicate_to_str(predicate, arg_strs)
            if predicate == "eq":
                if all(nnone_conditions):
                    nnone_compress = []
                    for nnone in nnone_conditions:
                        x = nnone[0]
                        for y in nnone:
                            x = self.connective_to_str('and', [x, y])
                        nnone_compress = x
                        neg_x = self.connective_to_str('neg', [x])
                    (nnone0, none0), (nnone1, none1) = nnone_compress
                    both_nnone = self.connective_to_str('and', [nnone0, nnone1])
                    both_none = self.connective_to_str('and', [none0, none1])
                    predicate_str = self.connective_to_str('and', [predicate_str, both_nnone])
                    predicate_str = self.connective_to_str('or', [predicate_str, both_none])
                    c = []
            for nnone in nnone_conditions:
                for c in nnone:
                    predicate_str = self.connective_to_str('and', [predicate_str, c])
            return predicate_str

        if debug: print("Unexpected function in boolean mode:", formula.f)
        return None

    def term_to_str(self, term, var_to_name, nnone_conditions, debug):

        var_name = var_to_name.get(term.f)
        if var_name is not None: return self.var_name_to_str(var_name)
        
        operation = self.operations.get(term.f, None)
        if operation is not None:
            arg_strs = []
            for arg in term.args:
                arg_str = self.term_to_str(arg, var_to_name, nnone_conditions, debug)
                if arg_str is None:
                    if debug: print("in:", arg)
                    return None
                arg_strs.append(arg_str)
            if operation in ('div', 'mod'):
                nonzero_divisor = self.connective_to_str("neg", [
                    self.predicate_to_str("eq", [
                        arg_strs[-1],
                        self.int_to_str(0)
                    ])
                ])
                nnone_conditions.append(nonzero_divisor)
            return self.operation_to_str(operation, arg_strs)

        if term.f.arity == 0: # number
            value = self.calculator.get_term_value(term)
            if isinstance(value, MathNumber) and value.x % 1 == 0:
                return self.int_to_str(int(value.x))

        if debug: print("Unexpected function in term mode:", term.f)
        return None

    def var_name_to_str(self, v): return v
    def int_to_str(self, n): return str(n)

    def connective_to_str(self, name, used_names): raise Exception("Not implemented")
    def predicate_to_str(self, name, used_names): raise Exception("Not implemented")
    def operation_to_str(self, name, used_names): raise Exception("Not implemented")
    def get_varname(self, name, used_names): raise Exception("Not implemented")
    def verify_str(self, formula_str, free_vars, time_limit, debug):
        raise Exception("Not implemented")

class IntHammerTFF(AbstractIntHammer):

    var_name_regex = re.compile("[A-Z][_a-zA-Z0-9]*")

    def connective_to_str(self, label, subterm_strs):
        if not subterm_strs: return {'true' : '$true', 'false' : '$false'}[label]
        if len(subterm_strs) == 1:
            assert label == 'neg'
            [A] = subterm_strs
            return f"(~ {A})"
        elif len(subterm_strs) == 2:
            conj = {
                'impl' : '=>',
                'and' : '&',
                'or' : '|',
                'xor' : '^',
                'equiv' : '<=>',
            }[label]
            A,B = subterm_strs
            return f"({A} {conj} {B})"
        else:
            raise Exception("Logical conjunction can take at most two arguments")

    def predicate_to_str(self, label, subterm_strs):
        A,B = subterm_strs
        if label == "eq": return f"({A} = {B})"
        else:
            pred_name = {
                'lt' : '$less',
                'le' : '$lesseq',
                'gt' : '$greater',
                'ge' : '$greatereq',
            }[label]
            return f"{pred_name}({A}, {B})"

    def operation_to_str(self, label, subterm_strs):
        op_name = {
            'uminus' : '$uminus',
            'plus' : '$sum',
            'minus' : '$difference',
            'times' : '$product',
            'div' : '$quotient_f',
            'mod' : '$remainder_f',
        }[label]
        return op_name+'('+','.join(subterm_strs)+')'

    def get_varname(self, name, used_names):
        if not self.var_name_regex.fullmatch(name):
            name = name.capitalize()
            if not self.var_name_regex.fullmatch(name):
                name = "VAR"
        if name in used_names:
            name = get_unused_name(name, used_names)
        return name
    
    def verify_str(self, formula_str, free_vars, time_limit, debug):
        if free_vars:
            quantifiers = [v+":$int" for v in free_vars]
            quantifiers = ', '.join(quantifiers)
            quantified_str = f"![{quantifiers}] : ({formula_str})"
        else:
            quantified_str = formula_str
        tptp_str = f"tff('pylogic_int_hammer_problem', conjecture, {quantified_str})."
        if debug: print(tptp_str)

        cmd = self.get_cmd(time_limit)
        if debug: print("cmd:", cmd)
        hammer_output = subprocess.run(
            cmd,
            input = tptp_str.encode(),
            capture_output = True,
        )
        hammer_output = hammer_output.stdout.decode() # get output string
        res = self.process_hammer_output(hammer_output)
        if not res and isinstance(debug, int) and debug > 5:
            if isinstance(debug, int) and debug > 5:
                    print(hammer_output)
        return res

class IntHammerSMT(AbstractIntHammer):

    var_name_regex = re.compile("[a-zA-Z][-_a-zA-Z0-9]*")
    label_to_smt_name = {
        'impl' : '=>',
        'neg' : 'not',
        'and' : 'and',
        'or' : 'or',
        'xor' : 'xor',
        'equiv' : '=',
        'true' : 'true',
        'false' : 'false',
        'lt' : '<',
        'le' : '<=',
        'gt' : '>',
        'ge' : '>=',
        'eq' : '=',
        'uminus' : '-',
        'plus' : '+',
        'minus' : '-',
        'times' : '*',
        'div' : 'divf',
        'mod' : 'modf',
    }

    def anything_to_str(self, label, subterm_strs):
        smt_name = self.label_to_smt_name[label]
        elements = [smt_name]+subterm_strs
        return '('+' '.join(elements)+')'
    def connective_to_str(self, *args): return self.anything_to_str(*args)
    def predicate_to_str(self, *args): return self.anything_to_str(*args)
    def operation_to_str(self, op, args):
        if op == "power":
            base,exp = args
            if not exp.isnumeric(): return None
            exp = int(exp)
            if not 0 <= exp <= 10: return None
            if exp == 0: return '1'
            res = base
            for _ in range(exp-1): res = self.operation_to_str('times', [res, base])
            return res
        else:
            return self.anything_to_str(op, args)

    def get_varname(self, name, used_names):
        if not self.var_name_regex.fullmatch(name):
            name = "aaa"
        name = get_unused_name(name, used_names)
        return name

    def lisp_lexer(self, lines): # simple version, ignoring strings for example
        for line in lines:
            i = line.find(';')
            if i >= 0: line = line[:i]
            parenth_pos = [m.start() for m in re.finditer('[()]', line)]
            last = 0
            for i in parenth_pos:
                yield from iter(line[last:i].split())
                yield line[i]
                last = i+1
            yield from iter(line[last:].split())
    def _lisp_parse_tokens(self, first_token, token_iter):
        if first_token == ')': raise Exception("unmatched parenthesis")
        elif first_token == '(':
            res = []
            for token in token_iter:
                if token == ')': break
                res.append(self._lisp_parse_tokens(token, token_iter))
            return res
        else:
            return first_token
    def lisp_parse_tokens(self, token_iter):
        return self._lisp_parse_tokens(next(token_iter), token_iter)
    def lisp_parse_lines(self, lines):
        return self.lisp_parse_tokens(self.lisp_lexer(lines))

    def verify_str(self, formula_str, free_vars, time_limit, debug):
        # we don't need unsat cores so far
        header = """
; (set-option :produce-unsat-cores true)
(set-logic NIA)
(define-fun divf ((a Int) (b Int)) Int (ite (< 0 b) (div a b) (- (div (- a) b))))
(define-fun modf ((a Int) (b Int)) Int (ite (< 0 b) (mod a b) (- (mod (- a) b))))
        """
        cmd = self.get_cmd(time_limit)
        if debug: print("cmd:", cmd)
        solver = subprocess.Popen(
            cmd,
            stdin = subprocess.PIPE, stdout = subprocess.PIPE,
            bufsize=1, universal_newlines=True
        )

        def feed_solver(x):
            if debug: print(x)
            solver.stdin.write(x+'\n')

        if debug: print("SMT input:")
        feed_solver(header)
        for v in free_vars:
            feed_solver(f"(declare-fun {v} () Int)")
        feed_solver(f"(assert (not {formula_str}))")
        feed_solver(f"(check-sat)")

        response = solver.stdout.readline().strip()
        if response == "sat":
            model_str,_ = solver.communicate("(get-model)")
            if debug:
                print("There is a counterexample")
                print("as string:")
                print(model_str)
            model_lisp = self.lisp_parse_lines(model_str.split('\n'))
            if model_lisp[0] == 'model':
                model_lisp = model_lisp[1:] # different for Z3 / CVC4
            if debug:
                print("as LISP:")
                print(model_lisp)
            res = {}
            for df,v,args,t,val in model_lisp:
                assert df == 'define-fun'
                assert args == []
                assert t == 'Int'
                res[v] = int(val)
            return res
        elif response == "unsat":
            solver.communicate()
            # long-term todo: remember unsat core
            return True
        else:
            solver.stdin.close()
            if debug: print(response)
            for line in solver.stdout:
                if debug: print(line, end = '')
            return None

class IntHammerCVC4(IntHammerSMT):
    def __init__(self, core, constants, calculator, cvc4_path = "cvc4"):
        super().__init__(core, constants, calculator)
        self.cvc4_path = cvc4_path
    def get_cmd(self, time_limit):
        cmd = [self.cvc4_path, '-m', '--lang', 'smt']
        if time_limit is not None:
            cmd.append(f"--tlimit={int(time_limit*1000)}")
        return cmd

class IntHammerZ3(IntHammerSMT):
    def __init__(self, core, constants, calculator, z3_path = "z3"):
        super().__init__(core, constants, calculator)
        self.z3_path = z3_path
    def get_cmd(self, time_limit):
        cmd = [self.z3_path, '-in']
        if time_limit is not None:
            cmd.append(f"-T:{time_limit}")
        return cmd

class IntHammerVampire(IntHammerTFF):
    def __init__(self, core, constants, calculator, vampire_path = "vampire"):
        super().__init__(core, constants, calculator)
        self.vampire_path = vampire_path
    def get_cmd(self, time_limit):
        cmd = [
            self.vampire_path,
            "--output_axiom_names", "on",
            "--proof", "tptp",
            "-sas", "z3",
        ]
        if time_limit is not None:
            cmd.extend(['-t', str(time_limit)+'s'])
        return cmd
    def process_hammer_output(self, hammer_output):
        return "% Refutation found." in hammer_output

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

    calculator.add_functions(
        parser.name_signature_to_const,
        LogicCalculation(),
        SetCalculation(),
        FunCalculation(),
        BinderCalculation(),
        CalculationNumbers(),
    )

    hammer_vampire = IntHammerVampire(
        core = core,
        constants = parser.name_signature_to_const,
        calculator = calculator,
        vampire_path = "/home/mirek/formal-math/vampire_z3_rel_static_HEAD_6295",
    )
    hammer_z3 = IntHammerZ3(
        core = core,
        constants = parser.name_signature_to_const,
        calculator = calculator,
    )
    hammer_cvc4 = IntHammerCVC4(
        core = core,
        constants = parser.name_signature_to_const,
        calculator = calculator,
    )

    problem_true = parser.parse_str("""
       n >= 0 =>
       x >= (n+1)*n//2 =>
       n <= (10 + (2 * (x // 36)))
    """)
    problem_false = parser.parse_str("""
       n >= 0 =>
       x >= (n+1)*n//2 =>
       n <= (10 + (2 * (x // 40)))
    """)
    problem_squares = parser.parse_str("""
       x^2 + y^2 = x^2 * y^2 => x = 0 && y = 0
    """)
    print("=====   Vampire  =====")
    thm = hammer_vampire.verify(problem_true, debug = False)
    print(thm)
    print("=====   Z3 provable  =====")
    thm = hammer_z3.verify(problem_true, debug = False)
    print(thm)
    print("=====   Z3 disprovable  =====")
    cex = hammer_z3.verify(problem_false, debug = False)
    print(cex)
    print(calculator.calculate(problem_false.substitute_free(cex)))
    print("=====   CVC4 provable  =====")
    thm = hammer_cvc4.verify(problem_true, debug = False)
    print(thm)
    print("=====   CVC4 disprovable  =====")
    cex = hammer_cvc4.verify(problem_false, debug = False)
    print(cex)
    print(calculator.calculate(problem_false.substitute_free(cex)))
    print("=====   CVC4 disprovable  =====")
    thm = hammer_cvc4.verify(problem_squares, debug = True)
    print(thm)
