from logic_core import AssumptionLabel, CoreTheorem
from term import Term, TermVariable, compose_substitutions, next_names
from unification import Unification

class Resolver:
    def run(self, label, core_thm): # returns resolved theorem, or a copy of itself
        raise Exception("Not implemented")
    @staticmethod
    def resolve_with(label, core_thm, proven_label):
        core_thm = core_thm.labels_to_impl(label)
        if isinstance(proven_label, Theorem):
            proven_label = proven_label.core_thm
        core_thm = core_thm.modus_ponens(proven_label)
        return core_thm

# Class for handling theorems in a coder-friendly way

class Theorem:
    def __init__(self, env, core_thm, frozen_vars = (), resolvers = ()):

        resolvers = list(resolvers)
        self.resolvers = []
        while resolvers:
            resolver, label = resolvers.pop()
            out = resolver.run(label, core_thm)
            if isinstance(out, CoreTheorem):
                core_thm = out
                resolvers.extend(self.resolvers)
                self.resolvers = []
            else:
                assert isinstance(out, Resolver), out
                self.resolvers.append((out, label))

        self.core_thm = core_thm
        self.frozen_vars = frozenset(frozen_vars)

        self._env = env
        self._name_to_var = dict()
        for v in core_thm.free_vars:
            v_ori = self._name_to_var.setdefault(v.name, v)
            if v_ori is not v and v.arity < v_ori.arity:
                self._name_to_var[v.name] = v
        self._rule_cache = dict()
        self._aux_labeled = None

    #
    #   Basic functions
    #

    def get_var(self, name):
        return self._name_to_var.get(name, None)

    def assumption(self, label):
        if not isinstance(label, AssumptionLabel):
            label = self._env._name_to_label.get(label, None)
        if label is None: return None
        return self.core_thm.assumption(label)

    @property
    def term(self): return self.core_thm.term
    @property
    def origin(self): return self.core_thm.origin
    @property
    def free_vars(self): return self.core_thm.free_vars
    @property
    def has_assumptions(self): return self.core_thm.has_assumptions

    def assump_items(self): return self.core_thm.assump_items()
    def assump_labels(self): return self.core_thm.assump_labels()
    def assumptions(self): return self.core_thm.assumptions()

    def to_str(self):
        res = self.core_thm.to_str()
        if self.frozen_vars:
            frozen_str = "Frozen: "+' '.join(map(str, self.frozen_vars))
            res = frozen_str+'\n'+res
        return res
    def __str__(self): return self.to_str()

    def exchange_frozen(self, frozen_vars):
        return Theorem(self._env, self.core_thm, frozen_vars, resolvers = self.resolvers)
    def unfreeze(self, vs = None):
        if vs is None:
            return self.exchange_frozen(())
        else:
            if isinstance(vs, (str, TermVariable)):
                vs = [vs]
            for v in vs:
                vs = [
                    v if not isinstance(v, str) else self.get_var(v)
                    for v in vs
                ]
                assert None not in vs
            return self.exchange_frozen(self.frozen_vars.difference(vs))
    def freeze(self, vs = None):
        if vs is None: vs = self.free_vars
        else:
            if isinstance(vs, (str, TermVariable)):
                vs = [vs]
            vs = [
                v if not isinstance(v, str) else self.get_var(v)
                for v in vs
            ]
            assert None not in vs
        return self.exchange_frozen(self.frozen_vars.union(vs))

    #
    #     Applying rules
    #
        
    def try_apply_rule(self, rule_name):
        if rule_name in self._rule_cache:
            return self._rule_cache[rule_name]
        rule_set = self._env.impl_rules[rule_name]
        res = rule_set.find_first(self)
        if res is not None: self._rule_cache[rule_name] = res        
        return res
    def apply_rule(self, rule_name):
        res = self.try_apply_rule(rule_name)
        if res is None:
            print(self)
            raise Exception(f"Failed to apply '{rule_name}': {self.term}")
        return res
    def to_impl(self):
        if self.term.f == self._env.core.implication:
            return self
        else:
            return self.apply_rule("to_impl")

    @property
    def symm(self):
        res = self.apply_rule("symm")
        res._rule_cache["symm"] = self
        return res
    def split(self):
        return self.apply_rule("split")

    def rw(self, *rules, **kwargs):
        return self._env.rewriter.run(self, *rules, **kwargs)

    #
    #    Basic operations
    #        

    def _aux_label_assump(self):
        if self._aux_labeled is not None: return self._aux_labeled
        label = AssumptionLabel("_AUX_")
        res = self.impl_to_labels(label)
        self._aux_labeled = res, label
        return self._aux_labeled
    def _aux_label_assumps(self, n):
        labels = []
        res = self
        for _ in range(n):
            res, label = res._aux_label_assump()
            labels.append(label)
        return res, labels
    def get_n_assumptions(self, n, keep_aux_labels = True):
        aterms = []
        aux_labels = []
        thm = self
        term = thm.core_thm.term
        for i in range(n):
            if term.f != self._env.core.implication:
                if i > 0:
                    thm, labels = thm._aux_label_assumps(i-len(aux_labels))
                    aux_labels.extend(labels)
                thm = thm.to_impl()
                term = thm.core_thm.term
            aterm, term = self._env.split_impl(term)
            aterms.append(aterm)
        if not keep_aux_labels:
            return thm, aterms, aux_labels
        if aux_labels:
            thm = thm.labels_to_impl(*labels)
        return thm, aterms
    
    def specialize(self, var_subst):
        if not var_subst: return self
        assert all(isinstance(x, Term) for x in var_subst.values())
        frozen_vars = self.frozen_vars
        substituted_vars = set(var_subst.keys())
        if any(substituted_vars & self.frozen_vars):
            frozen_vars = self.frozen_vars - substituted_vars
        var_subst = {
            var : term
            for var, term in var_subst.items()
            if var in self.core_thm.free_vars and not term.equals_to(var.to_term())
        }
        core_thm = self.core_thm
        if var_subst:
            core_thm = core_thm.specialize(var_subst)
        elif frozen_vars == self.frozen_vars: return self

        return Theorem(self._env, core_thm, frozen_vars, resolvers = self.resolvers)

    def relabel(self, relabeling):
        if not relabeling: return self
        relabeling = {
            label1 : label2
            for label1, label2 in relabeling.items()
            if label1 != label2
        }
        if not relabeling: return self
        assump_compressed = dict()
        to_unify = []
        for label_ori, aterm in self.core_thm.assump_items():
            label_new = relabeling.get(label_ori, label_ori)
            aterm_ori = assump_compressed.setdefault(label_new, aterm)
            if not (aterm_ori is aterm or aterm_ori.equals_to(aterm)):
                to_unify = assump, assump_ori, label_new
        res_thm = self.core_thm
        if to_unify:
            unification = Unification(frozen = [self.frozen_vars])
            for a,b,label in to_unify:
                unification.add_requirement(
                    a,0,b,0,
                    label = f"Unify label {label.name}:",
                )
            if not unification.run():
                unification.print_requirements()
                raise Exception("Unification failed")
            [subst] = unification.export_substitutions([self.core_thm.free_vars])
            res_thm = res_thm.specialize(subst)
        res_thm = res_thm.relabel(relabeling)

        if not self.resolvers: resolvers = []
        else:
            resolvers_d = dict(
                (relabeling.get(label, label), resolver)
                for resolver, label in self.resolvers
            )
            resolvers = [(resolver, label) for label, resolver in resolvers_d.items()]

        return Theorem(self._env, res_thm, self.frozen_vars, resolvers = resolvers)

    def labels_to_impl(self, *labels):
        if len(labels) == 1 and isinstance(labels[0], (list, tuple)):
            [labels] = labels
        if not labels: return self
        labels = [self._env.to_label(label) for label in labels]
        core_thm = self.core_thm.labels_to_impl(*labels)
        resolvers = [
            (resolver, label)
            for resolver, label in self.resolvers
            if label not in labels
        ]
        return Theorem(self._env, core_thm, self.frozen_vars, resolvers = resolvers)

    def impl_to_labels_basic(self, *labels):
        if len(labels) == 1 and isinstance(labels[0], (list, tuple)):
            [labels] = labels
        if not labels: return self
        core_thm = self.core_thm.impl_to_labels(*labels)
        return Theorem(self._env, core_thm, self.frozen_vars, resolvers = self.resolvers)
        
    def impl_to_labels(self, *labels):
        if len(labels) == 1 and isinstance(labels[0], (list, tuple)):
            [labels] = labels
        if not labels: return self
        env = self._env
        labels = [self._env.to_label(label) for label in labels]
        thm = self
        thm, assumptions = thm.get_n_assumptions(len(labels))
        assert all(isinstance(terma, Term) for terma in assumptions)
        if (any(label in thm.core_thm.assump_labels()
                for label in labels) # clashes -> unification
            or len(set(labels)) != len(labels)):

            res_assump = dict(thm.core_thm.assump_items())
            unification = Unification([self.frozen_vars])
            for label,terma in zip(labels, assumptions):
                terma_ori = res_assump.setdefault(label, terma)
                if terma_ori is not terma:
                    unification.add_requirement(
                        term,0, terma_ori,0,
                        label = f"Unify label {label.name}:",
                    )
            if not unification.run():
                unification.print_requirements()
                raise Exception("Unification failed")
            [subst] = unification.export_substitutions([self.core_thm.free_vars])
            thm = thm.specialize(subst)
        thm = thm.impl_to_labels_basic(*labels)
        return thm

    def _get_free_label(self, label, aterm, assump_final): # label must be changed, 
        aterm_ori = assump_final.get(label, aterm)
        if aterm_ori is aterm or aterm_ori.equals_to(aterm): return label
        for name in next_names(label.name):
            label = self._env.to_label(name)
            aterm_ori = assump_final.get(label, aterm)
            if aterm_ori.equals_to(aterm): return label
    
    def modus_ponens_basic(self, other, avoid_label_clashes = True):
        core_thm = self.core_thm
        other_thm = other.core_thm
        if avoid_label_clashes:
            if set(self.core_thm.assump_labels()) & set(other.core_thm.assump_labels()):
                renaming1 = dict()
                renaming2 = dict()
                assump_final = dict()
                for label, aterm in other.core_thm.assump_items():
                    if label in assump_final:
                        label_new = self._get_free_label(label, aterm, assump_final)
                        if label_new is not label:
                            renaming2[label] = label_new
                    assump_final[label] = aterm
                for label, aterm in self.core_thm.assump_items():
                    if label in assump_final:
                        label_new = self._get_free_label(label, aterm, assump_final)
                        if label_new is not label:
                            renaming1[label] = label_new
                        label = label_new
                    assump_final[label] = aterm
                if renaming1: core_thm = core_thm.relabel(renaming1)
                if renaming2: other_thm = other_thm.relabel(renaming2)

        core_thm = self.core_thm.modus_ponens(other_thm)
        if not self.resolvers:
            resolvers = other.resolvers
        elif not other.resolvers:
            resolvers = self.resolvers
        else:
            resolvers_d = { l : r for r,l in self.resolvers }
            resolvers_d.update((l,r) for r,l in other.resolvers)
            resolvers = [(r,l) for l,r in resolvers_d.items()]

        return Theorem(self._env, core_thm,
                       self.frozen_vars | other.frozen_vars,
                       resolvers)

    def set_resolver(self, resolver, label = "_AUTO_"):
        label = self._env.to_label(label)
        resolvers = list(self.resolvers)
        core_thm = self.core_thm
        if label in self.assump_labels():
            for i,(r,l) in enumerate(self.resolvers):
                if l == label:
                    resolvers[i] = resolver, label
                    break
            else:
                resolvers.append((resolver, label))
        else:
            core_thm = core_thm.impl_to_labels(label)
            resolvers.append((resolver, label))
        return Theorem(self._env, core_thm, self.frozen_vars, resolvers)

    #
    #   More advanced operations
    #

    def alpha_equiv_exchange(self, term):
        return self._env.basic_impl.refl(term).modus_ponens_basic(self)
    
    def generalize(self, *vs, fix_bnames = True, **kwargs):
        vs = [
            v if not isinstance(v, str) else self.get_var(v)
            for v in vs
        ]
        if len(set(vs)) != len(vs):
            raise Exception(f"Duplicite variable: {vs}")
        res = self
        correct_bnames = True
        res_term = self.term.substitute_free({
            v : Term(i)
            for i,v in zip(range(len(vs),0,-1), vs)
        })
        for v in reversed(vs):
            if isinstance(v, str): v = self.get_var(v)
            res = self._env.generalize(res, v, **kwargs)
            res_term = Term(self._env.constants.forall, (res.term.args[0],), ((v.name,),))
            if v.name != res.term.bound_names[0][0]: correct_bnames = False
        if not correct_bnames and fix_bnames:
            res = res.alpha_equiv_exchange(res_term)
        return res

    #
    #    The complex Call method
    #
    #    * label renaming
    #    * label positioning
    #    * resolving labeled assumption
    #    * resolving positional assumption
    #    * variable substitution
    #    * postponed: variable generalization
    #    * postponed: variable specialization
    #
    
    def __call__(self, *args, **kwargs):

        # (0) Analyze keyword arguments
        # #  var_name = var_value (string or term)
        # #  assump_name = new_name
        # #  assump_name = position
        # #  assump_name = theorem
        # mid-term postponed:
        # #  var = position   (generalization)
        # #  call on forall   (forall specify)

        out_pos_set = set()         # set(int) -- output positions
        relabeling = dict()         # { AssumptionLabel | AssumptionLabel }
        label_to_position = []      # list[ AssumptionLabel, int ]
        label_closing = dict()      # { AssumptionLabel | int -> Theorem }
        var_subst = dict()          # { TermVariable  ->   Term }
        for name, arg in kwargs.items():
            assump = self.assumption(name)
            if assump is not None:
                label = self._env.to_label(name)
                if isinstance(arg, (str, AssumptionLabel)):
                    relabeling[label] = self._env.to_label(arg)
                elif isinstance(arg, int):
                    assert arg >= 0
                    out_pos_set.add(arg)
                    label_to_position.append((label, arg))
                else:
                    assert isinstance(arg, Theorem)
                    label_closing[label] = arg
            else:
                v = self.get_var(name)
                if v is not None:
                    if isinstance(arg, int):
                        raise Exception("Positioning variables not supported yet")
                    else:
                        arg = self._env.to_term(arg, allow_binders = True)
                        var_subst[v] = arg
                else:
                    raise Exception(f"Unexpected keyword arguments: {name}")

        # (1) assure output positions are complete

        for arg in args:
            if isinstance(arg, int):
                assert arg >= 0
                out_pos_set.add(arg)
        if not out_pos_set: out_pos_num = 0
        else:
            out_pos_num = max(out_pos_set) + 1
            if out_pos_num != len(out_pos_set):
                args = list(args)
                for i in range(out_pos_num):
                    if i not in out_pos_set:
                        args.append(i)
        del out_pos_set

        # (2) find labels to merge

        to_glue_in_main = []

         # AssumptionLabel -> AssumptionLabel | int, to detect duplicities
        next_label_to_term = dict()

        for label1, label2 in relabeling.items():
            aterm = self.core_thm.assumption(label1)
            aterm2 = next_label_to_term.setdefault(label2, aterm)
            if aterm2 is not aterm:
                to_glue_in_main.append((aterm2, aterm))

        # (3) convert label_to_position to list of output labels
        # continue label merging

        out_pos_labels = [None] * out_pos_num
        out_pos_terms = [None] * out_pos_num
        for label, i in label_to_position:
            if out_pos_terms[i] is None:
                out_pos_labels[i] = label
                out_pos_terms[i] = self.core_thm.assumption(label)
            else:
                ori_label = out_pos_labels[i]
                aux_label = relabeling.get(ori_label, None)
                if aux_label is None:
                    aux_label = AssumptionLabel()
                    relabeling[ori_label] = aux_label
                relabeling[label] = aux_label
                to_glue_in_main.append((
                    self.assumption(label),
                    out_pos_terms[i],
                ))
        del label_to_position

        # (4) convert to implication, extract sides

        in_pos_num = len(args)
        main = self   # Theorem
        main, in_pos_aterms = main.get_n_assumptions(in_pos_num)

        # (5) Analyze positional arguments
        # #   assump_name -> put to named positions
        # #   position : int -> reposition
        # #   theorem -> apply modus ponens 
        # mid-term postponed:
        # #   term / str on position of a variable

        in_pos_data = [] # list[Theorem | AssumptionLabel]

        for i,(arg,aterm) in enumerate(zip(args, in_pos_aterms)):
            if isinstance(arg, (str, AssumptionLabel)):
                label = self._env.to_label(arg)
                aterm_ori = next_label_to_term.setdefault(label, aterm)
                if aterm_ori is not aterm:
                    to_glue_in_main.append((aterm, aterm_ori))
                in_pos_data.append(label)
            elif isinstance(arg, int):
                assert arg >= 0
                if out_pos_labels[arg] is None:
                    label = AssumptionLabel()
                    out_pos_labels[arg] = label
                    out_pos_terms[arg] = aterm
                else:
                    label = out_pos_labels[i]
                    label = relabeling.get(label, label)
                    to_glue_in_main.append((
                        aterm,
                        out_pos_terms[i],
                    ))
                in_pos_data.append(label)
            else:
                assert isinstance(arg, Theorem)
                in_pos_data.append(arg)

        del next_label_to_term
        del out_pos_terms

        # (6) make labels_closing positional, update in_pos_XXX

        label_closing = list(label_closing.items())
        closing_labels = [label for label,thm in label_closing]
        closing_label_thms = [thm for label,thm in label_closing]
        in_pos_num += len(closing_label_thms)
        in_pos_data = list(closing_label_thms) + in_pos_data
        in_pos_aterms = [
            main.core_thm.assumption(label)
            for label in closing_labels
        ] + in_pos_aterms
        main = main.labels_to_impl(*closing_labels)

        del label_closing
        del closing_labels
        del closing_label_thms

        # (7) unify variables

        if any(isinstance(x, Theorem) for x in in_pos_data) or to_glue_in_main:
            frozen_per_side = [ main.frozen_vars ]
            vars_per_side = [ main.core_thm.free_vars ]
            to_match = []
            for thm, aterm in zip(in_pos_data, in_pos_aterms):
                if not isinstance(thm, Theorem): continue
                frozen_per_side.append( thm.frozen_vars )
                vars_per_side.append( thm.core_thm.free_vars )
                to_match.append((aterm, thm.core_thm.term))

            unification = Unification(frozen = frozen_per_side)
            for a,b in to_glue_in_main:
                unification.add_requirement(a,0,b,0)
            for i,(a,b) in enumerate(to_match):
                unification.add_requirement(a,0,b,i+1)            
            if not unification.run():
                unification.print_requirements()
                raise Exception("Unification failed")
            substs = unification.export_substitutions(
                vars_per_side,
                self._env.get_locally_fresh_var,
            )

            # update substs with explicit substitution var_subst

            custom_subst = dict()
            for v,t in var_subst.items():
                t_unif = substs[0].get(v, None)
                if t_unif is not None:
                    if not (isinstance(t_unif.f, TermVariable) and
                            t_unif.f.to_term().equals_to(t_unif)):
                        raise Exception(f"Cannot assign variable {v}, already set by unification to {t_unif}")
                    v = t_unif.f
                if v in custom_subst:
                    t2 = custom_subst[v]
                    raise Exception(f"Cannot variable {v} double assigned: {t}, {t2}")
                custom_subst[v] = t

            substs = [
                compose_substitutions(subst, custom_subst)
                for subst in substs
            ]

            # apply substitutions
            
            subst_it = iter(substs)
            main = main.specialize(next(subst_it))

            for i,thm in enumerate(in_pos_data):
                if not isinstance(thm, Theorem): continue
                in_pos_data[i] = thm.specialize(next(subst_it))
        else:
            main = main.specialize(var_subst)

        del in_pos_aterms
        del to_glue_in_main

        # (8) relabel theorems (from the last one)

        to_merge = []
        assump_final = dict()
        _, aterms = main.get_n_assumptions(in_pos_num)
        for i in reversed(range(in_pos_num)):
            x = in_pos_data[i]
            if isinstance(x, AssumptionLabel):
                aterm_ori = assump_final.get(x, aterm)
                if aterm_ori is aterm or aterm_ori.equals_to(aterm):
                    assump_final[x] = aterm
                else:
                    to_merge.append([aterm, aterm_ori])
            else:
                thm_relabeling = dict()
                for label, aterm in x.core_thm.assump_items():
                    if label in assump_final:
                        label_new = self._get_free_label(label, aterm, assump_final)
                        if label_new is not label:
                            thm_relabeling[label] = label_new
                        label = label_new
                    assump_final[label] = aterm
                in_pos_data[i] = x.relabel(thm_relabeling)

        # (9) relabel main
        # # to avoid assump_final
        # # to respect relabeling
        # # to merge positional labels
        # # update out_pos_labels

        # check relabeling values, create assump_final2
        assump_final2 = dict()
        for label1, label2 in relabeling.items():
            assump_final2[label2] = main.core_thm.assumption(label1)
        for label, aterm in assump_final.items():
            aterm_ori = assump_final2.setdefault(label, aterm)
            if not (aterm_ori is aterm or aterm_ori.equals_to(aterm)):
                to_merge.append((aterm_ori, aterm))
        for label, aterm in main.core_thm.assump_items():
            if label in relabeling: continue
            if label in assump_final:
                label_new = self._get_free_label(label, aterm, assump_final)
                if label_new is not label:
                    relabeling[label] = label_new
                    label = label_new
                assump_final[label] = aterm
                aterm_ori = assump_final2.setdefault(label, aterm)
                if not (aterm_ori is aterm or aterm_ori.equals_to(aterm)):
                    to_merge.append((aterm_ori, aterm))

        main = main.relabel(relabeling)
        out_pos_labels = [
            relabeling.get(label, label)
            for label in out_pos_labels
        ]

        # (10) another unification based on relabeling (if necessary)

        if to_merge:
            unification = Unification([ main.frozen_vars ])
            for a,b in to_merge:
                unification.add_requirement(a,0,b,0)
            if not unification.run():
                unification.print_requirements()
                raise Exception("Unification failed")
            [subst] = unification.export_substitutions(
                [self.core_thm.free_vars],
            )
            main = main.specialize(subst)
            for i,thm in enumerate(in_pos_data):
                if not isinstance(thm, Theorem): continue
                in_pos_data[i] = in_pos_data[i].specialize(subst)

        # (11) Apply modus ponens / take labeled arguments
        
        cur_labels_to_take = []
        for thm_or_label in in_pos_data:
            if isinstance(thm_or_label, Theorem):
                if cur_labels_to_take:
                    main = main.impl_to_labels_basic(*cur_labels_to_take)
                    cur_labels_to_take = []
                main = main.modus_ponens_basic(thm_or_label, False)
            else:
                cur_labels_to_take.append(thm_or_label)
        if cur_labels_to_take:
            main = main.impl_to_labels_basic(*cur_labels_to_take)

        del cur_labels_to_take
        del in_pos_data

        # (12) Explicit assumption positions

        main = main.labels_to_impl(*out_pos_labels)
        return main
