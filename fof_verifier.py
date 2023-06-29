import re
import itertools
from collections import deque
from weakref import WeakValueDictionary, WeakSet
from term import Term, TermApp, BVar, TermVariable, TermConstant, get_unused_name
from share_term import TermCache
import subprocess
from logic_core import Verifier, CoreTheorem, Proof

class ProofFofHammer(Proof):
    def __init__(self, used_axioms):
        self.used_axioms = used_axioms

class HigherOrderStatement:
    def __init__(self, term, metadata, exporter):
        self.term = exporter.share_term(term)

        self.hvs = [
            v for v in term.get_ordered_free_vars()
            if v.arity > 0
        ]
        self.bi_to_vs = dict()
        self._examine_input_vars(term)
        self.bis_per_hv = [[] for _ in self.hvs]
        hv_to_index = { v : i for i,v in enumerate(self.hvs) }
        for bi, vs in self.bi_to_vs.items():
            for v in vs:
                self.bis_per_hv[hv_to_index[v]].append(bi)
        self.used_instantiations = set()
        self.metadata = metadata
        self.exporter = exporter
        self.inst_limit = exporter.config.instantiation_limit

    def _examine_input_vars(self, term): # sets self.input_vars : TermVariable -> [(binder, i), ...]
        if not any(v.arity > 0 for v in term.free_vars): return
        for i,(bnum,arg) in enumerate(zip(term.f.signature, term.args)):
            if (bnum > 0 and arg.is_free_var and
                arg.f.arity == bnum and arg.equals_to(arg.f.to_term())):
                bi = (term.f, i)
                vs = self.bi_to_vs.setdefault(bi, [])
                if arg.f not in vs: vs.append(arg.f)
            self._examine_input_vars(arg)

    def instantiate(self):
        if self.inst_limit == 0: return
        instances_per_hv = [
            list(itertools.chain.from_iterable(
                self.exporter.bi_to_instances.get(bi, [[]])[0]
                for bi in bis
            ))
            for bis in self.bis_per_hv
        ]
        for inst_tuple in itertools.product(*instances_per_hv):
            if inst_tuple in self.used_instantiations: continue
            self.used_instantiations.add(inst_tuple)
            inst_tuple_fresh = map(self.make_vars_fresh, inst_tuple)
            subst = dict(zip(self.hvs, inst_tuple_fresh))
            statement = self.term.substitute_free(subst)
            self.exporter.add_basic_statement(statement, self.metadata)
            self.inst_limit -= 1
            if self.inst_limit == 0: return
    
    def could_be_instantiated(self):
        return self.inst_limit == 0 or all(self.bis_per_hv)

    def make_vars_fresh(self, term):
        if not term.free_vars: return term
        return term.substitute_free({
            v : TermVariable(v.arity, v.name).to_term()
            for v in term.free_vars
        })
    
class HigherToFirstOrder:
    def __init__(self, config, take_fof_fun):

        self.config = config
        self.take_fof_fun = take_fof_fun

        self.term_cache = TermCache()
        self.term_to_fof_cache = dict()
        self.i_arity_to_var = dict()

        self.basic_statements = []
        self.basic_statements_set = set()

        self.to_instantiate = deque()
        self.to_instantiate_set = set()
        self.ho_statements = []

        self.bi_to_statements = dict() # (binder, i) -> (ho_statements, var)
        self.bi_to_instances = dict() # (binder, i) -> (terms_l, terms_s)
        self.definitions = dict() # (term_key, label) -> term_head

        # to_bool(true)
        self.add_fof_statement(
            config.c_to_bool(config.c_true())
        )
        # !to_bool(false)
        self.add_fof_statement(
            config.c_neg(config.c_to_bool(config.c_false()))
        )

    def add_statement(self, statement, metadata):
        self.new_fof = []
        if any(v.arity > 0 for v in statement.free_vars):
            statement = HigherOrderStatement(statement, metadata, self)
            if not statement.could_be_instantiated(): return
            for bi in statement.bi_to_vs.keys():
                statements = self.bi_to_statements.setdefault(bi, [])
                statements.append(statement)
            self.ho_statements.append(statement)
            statement.instantiate()
        else:
            self.add_basic_statement(statement, metadata)
        self.ho_instantiation_update()
        return self.new_fof

    def add_bi_instance(self, binder, index, instance):
        bi = binder, index
        if bi in self.bi_to_instances:
            instances_list, instances_set = self.bi_to_instances[bi]
        else:
            instances_list, instances_set = [], set()
            self.bi_to_instances[bi] = instances_list, instances_set
        instance_key = self.share_term(instance, rename = True)
        if instance_key in instances_set: return

        instances_list.append(instance)
        instances_set.add(instance_key)

        for ho_statement in self.bi_to_statements.get(bi, ()):
            if ho_statement in self.to_instantiate_set: continue
            self.to_instantiate.append(ho_statement)
            self.to_instantiate_set.add(ho_statement)
        
    def share_term(self, term, rename = False):
        if rename:
            subst = {
                v : self.i_arity_to_var.setdefault(
                    (i, v.arity),
                    TermVariable(v.arity, v.name)
                ).to_term()
                for i,v in enumerate(term.get_ordered_free_vars())
            }
            term = term.substitute_free(subst)
        return self.term_cache.share(term)

    def ho_instantiation_update(self):
        while self.to_instantiate:
            self.to_instantiate.popleft().instantiate()

    def add_basic_statement(self, statement, metadata):
        statement_key = self.share_term(statement, rename = True)
        if statement_key in self.basic_statements_set: return
        self.basic_statements_set.add(statement_key)
        self.add_fof_statement(self.term_to_fof(statement, 0), metadata)

    def add_fof_statement(self, statement, metadata = None):
        statement_key = self.share_term(statement, rename = True)
        self.basic_statements_set.add(statement_key)
        self.basic_statements.append((statement, metadata))
        self.take_fof_fun(statement, metadata)

    def term_to_fof(self, term, ctx):
        res = self.term_to_fof_cache.get((term, ctx), None)
        if res is not None: return res

        # ctx = 0 -- bool
        # ctx = 1 -- under forall
        # ctx = 2 -- term
        term_is_bool = isinstance(term, TermApp) and term.f in self.config.out_bool
        term_can_be_bool = term_is_bool or (isinstance(term, TermApp) and (
            term.f in (self.config.c_require, self.config.c_true, self.config.c_false)
        ))
        if ctx == 0 and not term_can_be_bool:
            res = TermApp(self.config.c_to_bool, (self.term_to_fof(term, 2),))
            self.term_to_fof_cache[term, ctx] = res
            return res
        elif ctx == 1 and not term_can_be_bool:
            res = TermApp(self.config.c_to_bool1, (self.term_to_fof(term, 2),))
            self.term_to_fof_cache[term, ctx] = res
            return res

        if term_is_bool and ctx == 2:
            term = self.term_to_fof(term, 0)
            def_data, res = self.replace_with_defined_raw(term, "bool_val", "bool_val")
            if def_data is not None:
                def_head, def_body = def_data
                self.add_fof_statement(self.config.c_impl( # term => bool_val = true
                    def_body,
                    self.config.c_eq(
                        def_head,
                        self.config.c_true(),
                    )
                ), None)
                self.add_fof_statement(self.config.c_impl( # !term => bool_val = false
                    self.config.c_neg(def_body),
                    self.config.c_eq(
                        def_head,
                        self.config.c_false(),
                    )
                ), None)

            self.term_to_fof_cache[term, ctx] = res
            return res

        if isinstance(term, BVar):
            self.term_to_fof_cache[term, ctx] = term
            return term
        f = term.f
        if f == self.config.c_to_bool:
            res = self.term_to_fof(term.args[0], 0)
            self.term_to_fof_cache[term, ctx] = res
            return res
        if f == self.config.c_to_bool1:
            res = self.term_to_fof(term.args[0], 1)
            self.term_to_fof_cache[term, ctx] = res
            return res

        inner_ctx = self.config.get_inner_ctx(f)
        if f == self.config.c_require:
            if ctx == 0:
                f = self.config.c_and
                inner_ctx = (0,0)
            elif ctx == 1:
                f = self.config.c_impl
                inner_ctx = (0,1)

        if f == self.config.c_eq:
            compared_bool = all(
                isinstance(x, TermApp) and (
                    x.f in self.config.out_bool or
                    x.f in (self.config.c_true, self.config.c_false)
                )
                for x in term.args
            )
            if compared_bool:
                f = self.config.c_equiv
                inner_ctx = [0,0]

        args = []
        for numb, arg, ictx in zip(f.signature, term.args, inner_ctx):
            if numb > 0 and ictx == 2:
                if isinstance(arg, TermApp) and arg.f in self.config.out_bool:
                    ictx = 0
            args.append(self.term_to_fof(arg, ictx))

        if all(x == 0 for x in f.signature) or f in (self.config.c_forall, self.config.c_exists):
            # the most standard case

            res = TermApp(f, args, term.bound_names)
            self.term_to_fof_cache[term, ctx] = res
            return res

        # replace the arguments with binders
        defined_binder_args = []
        final_subst = dict()
        for i,(numb, arg) in enumerate(zip(f.signature, args)):
            if numb == 0:
                v = TermVariable(0)
                final_subst[v] = arg
                defined_binder_args.append(v.to_term())
            else:
                arg = self.replace_with_defined(arg)
                # for storing definition, replace arg.bvars > numb
                # with free variables
                if arg.debruijn_height > numb:
                    bound_subst = [None] + [
                        BVar(i) for i in range(1,numb+1)
                    ] + [
                        TermVariable(0).to_term()
                        for _ in range(numb+1, arg.debruijn_height+1)
                    ]
                    arg2 = arg.substitute_bvars(bound_subst, natural_order = False)
                else:
                    arg2 = arg
                self.add_bi_instance(f,i,arg2)

                defined_binder_args.append(arg)

        def_data, res = self.replace_with_defined_raw(
            TermApp(f, defined_binder_args, term.bound_names),
            f.name,
            "binder",
        )
        if def_data is not None and f in self.config.out_bool:
            def_head, def_body = def_data
            self.config.out_bool.add(def_head.f)
        if final_subst:
            res = res.substitute_free(final_subst)
        
        self.term_to_fof_cache[term, ctx] = res
        return res

    def replace_with_defined_raw(self, term, def_name, def_label):

        if not term.is_closed:
            final_subst = dict()
            bound_subst = [None]*(term.debruijn_height+1)
            for i in term.bound_vars:
                v = TermVariable(0)
                bound_subst[i] = v.to_term()
                final_subst[v] = BVar(i)
            def_body = term.substitute_bvars(bound_subst, natural_order = False)
        else:
            def_body = term
            final_subst = dict()

        body_key = self.share_term(def_body, rename = True)
        def_head = self.definitions.get((body_key, def_label), None)
        body_vs = def_body.get_ordered_free_vars()
        
        if def_head is None:
            assert all(v.arity == 0 for v in body_vs)
            defined_constant = TermConstant((0,)*len(body_vs), name = def_name)
            def_head = defined_constant(*(v.to_term() for v in body_vs))
            self.definitions[body_key, def_label] = def_head
            def_data = def_head, def_body
        else:
            def_data = None
            final_subst.update({
                key_var : final_subst.get(body_var, body_var.to_term())
                for key_var, body_var in zip(def_head.get_ordered_free_vars(), body_vs)
            })

        if not final_subst: replacement = def_head
        else: replacement = def_head.substitute_free(final_subst)

        return def_data, replacement

    def replace_with_defined(self, term):
        if isinstance(term, BVar): return term

        # if term is simple, no replacement
        if term.is_const and all(x == 0 for x in term.f.signature):
            if all(isinstance(arg, BVar) or (isinstance(arg.f, TermVariable) and arg.f.arity == 0)
                   for arg in term.args):
                if len(term.bound_vars) + len(term.free_vars) == len(term.args):
                    return term

        if term.f in self.config.out_bool:
            def_connective = self.config.c_equiv
            defined_pred = True
            def_name = "pred"
        else:
            def_connective = self.config.c_eq
            defined_pred = False
            def_name = "body"

        def_data, res = self.replace_with_defined_raw(term, def_name, "main")
        if def_data is not None:
            def_head, def_body = def_data
            if defined_pred:
                self.config.out_bool.add(def_head.f)
            self.add_fof_statement(
                def_connective(def_head, def_body),
                None,
            )
        return res

class HigherToFirstOrderConfig:
    def __init__(self, const_dir, instantiation_limit = 24):
        self.instantiation_limit = instantiation_limit

        self.c_require = const_dir["_require", (0,0)]
        self.c_true = const_dir["true", ()]
        self.c_false = const_dir["false", ()]

        self.c_is_bool = const_dir["_is_bool", (0,)]
        self.c_to_bool = const_dir["to_bool", (0,)]
        self.c_to_bool1 = const_dir["to_bool1", (0,)]

        self.c_impl = const_dir["__impl__", (0,0)]
        self.c_eq = const_dir["__eq__", (0,0)]
        self.c_neg = const_dir["_neg", (0,)]
        self.c_and = const_dir["_and", (0,0)]
        self.c_or = const_dir["_or", (0,0)]
        self.c_xor = const_dir["_xor", (0,0)]
        self.c_equiv = const_dir["_equiv", (0,0)]
        self.c_forall = const_dir["forall", (1,)]
        self.c_exists = const_dir["exists", (1,)]

        self._inner_ctx = {
            self.c_impl : [0,0],
            self.c_neg : [0],
            self.c_and : [0,0],
            self.c_or : [0,0],
            self.c_xor : [0,0],
            self.c_equiv : [0,0],
            self.c_forall : [1],
            self.c_exists : [0],
        }

        self.out_bool = WeakSet([
            self.c_is_bool,
            self.c_to_bool,
            self.c_to_bool1,
            self.c_eq,
        ])
        self.out_bool.update(self._inner_ctx.keys())

    def get_inner_ctx(self, f):
        res = self._inner_ctx.get(f, None)
        if res is not None: return res
        res = [2]*f.arity
        self._inner_ctx[f] = res
        return res

class FirstOrderToTPTP:
    def __init__(self, config):
        self.config = config
        self.last_index = 0
        self.const_to_name = dict()
        self.used_const_names = set()
        # to prevent catching parts of a term as a conjecture description
        self.used_const_names.add("file")
        self.thm_name_to_metadata = dict()

        self.used_var_names = None
        self.var_to_name = None
        self.bound_names = None

    def export_fof(self, formula, metadata = None, thm_label = "axiom"):
        self.last_index += 1
        thm_name = f"statement_{self.last_index}"
        self.thm_name_to_metadata[thm_name] = metadata

        vs = formula.get_ordered_free_vars()
        assert all(v.arity == 0 for v in vs)
        self.used_var_names = set()
        self.var_to_name = {
            v : self._get_var_name(v.name)
            for v in vs
        }
        self.bound_names = []
        formula_str = self._formula_to_str(formula)
        if self.var_to_name:
            vs_names = ','.join(self.var_to_name.values())
            formula_str = f"![{vs_names}] : {formula_str}"
        self.used_var_names = None
        self.var_to_name = None
        self.bound_names = None

        return f"fof('{thm_name}', {thm_label}, {formula_str}).\n"

    def _formula_to_str(self, formula):
        assert isinstance(formula, TermApp)
        if formula.f in self.config.quantifiers:
            [[bname]] = formula.bound_names
            bname = self._get_var_name(bname)
            self.bound_names.append(bname)
            [body] = formula.args
            body_str = self._formula_to_str(body)
            self.bound_names.pop()
            self.used_var_names.remove(bname)
            q = self.config.quantifiers[formula.f]
            return f"{q}[{bname}] : {body_str}"
        elif formula.f in self.config.connectives:
            args_str = [self._formula_to_str(arg) for arg in formula.args]
            tokens = [
                (token if isinstance(token, str) else args_str[token])
                for token in self.config.connectives[formula.f]
            ]
            return '('+' '.join(tokens)+')'
        elif formula.f == self.config.c_eq:
            a,b = formula.args
            a_str = self._term_to_str(a)
            b_str = self._term_to_str(b)
            return f"({a_str} = {b_str})"
        else:
            pred_name = self._get_const_name(formula.f)
            assert all(numb == 0 for numb in formula.f.signature)
            args = [self._term_to_str(arg) for arg in formula.args]
            if not args: return pred_name
            else: return pred_name + '(' + ','.join(args) + ')'

    def _term_to_str(self, term):
        if isinstance(term, BVar):
            return self.bound_names[-term.debruijn_height]
        elif term.is_free_var:
            return self.var_to_name[term.f]
        else:
            f_name = self._get_const_name(term.f)
            assert all(numb == 0 for numb in term.f.signature)
            args = [self._term_to_str(arg) for arg in term.args]
            if not args: return f_name
            else: return f_name + '(' + ','.join(args) + ')'
    
    def _get_var_name(self, name):
        name = name.strip('_')
        if not self.config.var_name_regex.fullmatch(name):
            if self.config.const_name_regex.fullmatch(name):
                name = name.capitalize()
            else: name = "VAR"
        if name in self.used_var_names:
            name = get_unused_name(name, self.used_var_names)
        self.used_var_names.add(name)
        return name

    def _get_const_name(self, const):
        name = self.const_to_name.get(const, None)
        if name is not None: return name
        name = const.name.strip('_')
        if not self.config.const_name_regex.fullmatch(name):
            if self.config.var_name_regex.fullmatch(name):
                name = name.lower()
            else: name = "const"
        if name in self.used_const_names:
            name = get_unused_name(name, self.used_const_names)
        self.used_const_names.add(name)
        self.const_to_name[const] = name
        return name

    def process_proof(self, prover_output):
        proof_found_reports = [
            "# Proof found!",      # E prover
            "% Refutation found.", # Vampire, who is Tanya by the way? :-)
        ]
        if not any(x in prover_output for x in proof_found_reports):
            return None

        # find used assumptions
        used = set()
        last_i = 0
        file_thm_name_start = " file("
        file_thm_name_end = "))."
        while True:
            i = prover_output.find(file_thm_name_start, last_i)
            if i < 0: break
            i += len(file_thm_name_start)
            i2 = prover_output.find(file_thm_name_end, i)
            assert i2 > 0
            last_i = i2+len(file_thm_name_end)
            file_thm_name = prover_output[i:i2]
            fname, thm_name = file_thm_name.split(',')
            thm_name = thm_name.strip().strip("'")
            metadata = self.thm_name_to_metadata[thm_name]
            if metadata is not None: used.add(metadata)
        return used

class FirstOrderToTPTPConfig:
    def __init__(self, const_dir):

        self.connectives = {
            const_dir["__impl__", (0,0)] : [0, '=>', 1],
            const_dir["_neg", (0,)] : ['~', 0],
            const_dir["_and", (0,0)] : [0,'&',1],
            const_dir["_or", (0,0)] : [0,'|',1],
            const_dir["_xor", (0,0)] : [0,'^',1],
            const_dir["_equiv", (0,0)] : [0,'<=>',1],
            const_dir["true", ()] : ['$true'],
            const_dir["false", ()] : ['$false'],
        }

        self.c_eq = const_dir["__eq__", (0,0)]
        self.quantifiers = {
            const_dir["forall", (1,)] : '!',
            const_dir["exists", (1,)] : '?',
        }

        self.const_name_regex = re.compile("[a-z][_a-zA-Z0-9]*")
        self.var_name_regex = re.compile("[A-Z][_a-zA-Z0-9]*")

class FofHammer(Verifier):
    def __init__(self, core, constants, solver_cmd, instantiation_limit = 24):
        super().__init__(core)
        self._to_fof_config = HigherToFirstOrderConfig(constants, instantiation_limit)
        self._tptp_config = FirstOrderToTPTPConfig(constants)
        self._c_is_bool = constants["_is_bool", (0,)]
        self._solver_cmd = solver_cmd

    def add_predicate(self, is_bool_thm):
        assert isinstance(is_bool_thm, CoreTheorem) and is_bool_thm._core == self.core
        assert not is_bool_thm.has_assumptions
        assert is_bool_thm.term.is_const and is_bool_thm.term.f == self._c_is_bool
        term = is_bool_thm.term.args[0]
        assert term.is_const
        assert all(
            arg.is_free_var and arg.equals_to(arg.f.to_term())
            for arg in term.args
        )
        assert len(set(arg.f for arg in term.args)) == len(term.args)
        self._to_fof_config.out_bool.add(term.f)

    def run(self, goal, axioms, verbose = False):
        assert isinstance(axioms, (tuple, list))
        assert all(isinstance(axiom, CoreTheorem) for axiom in axioms)
        assert isinstance(goal, Term)

        label_to_assump = dict()
        for axiom in axioms:
            for label, assump in axiom.assump_items():
                assump_ori = label_to_assump.set_default(label, assump)
                if not assump_ori.equals_to(assump):
                    print(f"label.name:")
                    print('  ', assump)
                    print('  ', assump_ori)
                    raise Exception("Labeled assumption conflict!")

        tptp_lines = []

        if verbose:
            print()
            print("First order formulae:")

        tptp_exporter = FirstOrderToTPTP(self._tptp_config)
        def take_fof_fun(term, metadata):
            if verbose: print('  ->', list(map(str, term.free_vars)), term)
            if metadata is None: thm_label, metadata = "axiom", None
            elif metadata < 0: thm_label, metadata = "conjecture", None
            else: thm_label, metadata = "axiom", metadata
            tptp_line = tptp_exporter.export_fof(term, metadata, thm_label)
            tptp_lines.append(tptp_line)

        to_fof = HigherToFirstOrder(self._to_fof_config, take_fof_fun)
        var_to_const_d = dict()

        for i,axiom in enumerate(axioms):
            assert isinstance(axiom, CoreTheorem)
            frozen_vs = set()
            for assump in axiom.assumptions():
                frozen_vs.add(assump.free_vars)
            frozen_term = self.var_to_const(axiom.term, frozen_vs, var_to_const_d)
            if verbose:
                print("<-", list(map(str, frozen_term.free_vars)), frozen_term)
            to_fof.add_statement(frozen_term, i)

        frozen_goal = self.var_to_const(goal, goal.free_vars, var_to_const_d)
        if verbose:
            print("<-", list(map(str, frozen_goal.free_vars)), frozen_goal)
        to_fof.add_statement(frozen_goal, -1)

        if verbose:
            print()
            print("In TPTP format:")
            for line in tptp_lines:
                print(line, end = '')
            print()

        problem_bytes = ''.join(tptp_lines).encode()
        solver_result = subprocess.run(
            self._solver_cmd,
            input = problem_bytes,
            capture_output = True,
        )
        solver_result_str = solver_result.stdout.decode()
        solver_out = tptp_exporter.process_proof(solver_result_str)

        if solver_out is None: return None # not proven

        used_axioms = tuple(
            axioms[i]
            for i in sorted(solver_out)
        )
        label_to_assump = dict()
        for axiom in used_axioms:
            for label, assump in axiom.assump_items():
                label_to_assump.set_default(label, assump)
        proof = ProofFofHammer(used_axioms)
        return self._make_thm(label_to_assump, goal, proof)

    @staticmethod
    def var_to_const(term, vs, var_to_const_d):
        vs = list(vs)
        if not vs: return term
        cs = []
        for v in vs:
            c = var_to_const_d.get(v, None)
            if c is None:
                c = TermConstant(v.signature, v.name)
                var_to_const_d[v] = c
            cs.append(c)
        return term.substitute_free({
            v : c.to_term()
            for v,c in zip(vs, cs)
        })

if __name__ == "__main__":
    from logic_env import LogicEnv
    env = LogicEnv()
    config = HigherToFirstOrderConfig(env.parser.name_signature_to_const)
    exporter = HigherToFirstOrder(config, lambda t,m: print(t,m))
    tt = env.to_term

    #exporter.add_statement(tt("forall(A : map_set(x : require x in A; x, B))"), 42)
    #exporter.add_statement(tt("map_set(x : require x in A; x, B)"), 5)
    #exporter.add_statement(tt("forall(A : map_set(x : require x in A; x, B))"), 42)
    exporter.add_statement("(PRED(X) && forall(y : PRED(y)  => y = X) => X = unique(x : PRED(x))) && (!exists(x : PRED(x)) || exists(x : exists(y : x != y && PRED(x) && PRED(y))) => unique(x : PRED(X)) = null)")
    exporter.add_statement("")
