from term import Term, TermApp, BVar, TermConstant, TermVariable
from logic_core import AssumptionLabel, DefinedConstant
from pattern_lookup import PatternLookupRewrite
from pytheorem import Theorem
from unification import Unification
from calculator import Calculator

class RootRewriter:
    def try_rw(self, term):
        raise Exception("Not implemented")
    def to_pattern(self):
        return None
    def to_pattern_rw(self):
        pattern = self.to_pattern()
        assert pattern is not None
        return RootRewriterPattern(pattern)

class RootRewriterPattern(RootRewriter):
    def __init__(self, pattern):
        assert isinstance(pattern, PatternLookupRewrite)
        self.pattern = pattern
    def try_rw(self, term):
        return self.pattern.find_first(term)
    def to_pattern(self):
        return self.pattern
    def to_pattern_rw(self):
        return self

class RootRewriterSingle(RootRewriter):
    def __init__(self, rule):
        self.rule = rule
        self.env = rule._env
        self.match_term, _ = self.env.split_eq(rule.term)
    def try_rw(self, term):
        unification = Unification((self.rule.frozen_vars, None))
        unification.add_requirement(self.match_term,0, term,1)
        if not unification.run(): return None
        subst,_ = unification.export_substitutions(
            [self.match_term.free_vars, term.free_vars],
        )
        return self.rule.specialize(subst)
    def to_pattern(self):
        pattern = PatternLookupRewrite()
        pattern = pattern.add_rule(self.rule)
        return pattern

class RootRewriterList(RootRewriter):
    def __init__(self, rewriters):
        self.rewriters = rewriters
    def try_rw(self, term):
        for rw in self.rewriters:
            res = rw.try_rw(term)
            if res is not None: return res
        return None
    def to_pattern(self):
        pattern = PatternLookupRewrite()
        for rw in self.rewriters:
            pattern = pattern.union(rw.to_pattern())
        return pattern

class RootRewriterUnfold(RootRewriter):
    def __init__(self, env, consts):
        self.env = env
        assert all(
            isinstance(c, DefinedConstant)
            for c in consts
        )
        self.to_unfold = set(consts)
    def try_rw(self, term):
        if term.f not in self.to_unfold: return None
        definition = term.f.def_thm
        A,B = self.env.split_eq(definition.term)
        subst = {
            A_arg.f : term_arg
            for A_arg, term_arg in zip(A.args, term.args)
        }
        return definition.specialize(subst)

class RootRewriterCalc(RootRewriter):
    def __init__(self, env, calculator):
        self.env = env
        self.calculator = calculator
    def try_rw(self, term):
        if not term.is_closed or term.free_vars: return None
        core_thm = self.calculator.calculate(term)
        if core_thm is None: return None
        term2 = core_thm.term.args[1]
        if term2.equals_to(term): return None # already simplfied
        thm = Theorem(self.env, core_thm)
        return thm

class Rewriter:
    def __init__(self, eq_refl, eq_cong): # X = Y => PRED(X) => PRED(Y)
        self._env = eq_cong._env
        self._eq_cong = self._check_eq_cong(eq_cong)
        self._eq_refl = self._check_eq_refl(eq_refl) # must be added after eq_cong -- expects self._X set

        # can be used for rewriting
        self._eq_to_impl = self._prove_eq_to_impl()   # X = Y => X => Y
        self._eq_cong_eq = self._prove_eq_cong_eq()   # X = Y => BODY(X) = BODY(Y)

        # using rewriting to prove
        self._eq_to_rimpl = self._prove_eq_to_rimpl() # X = Y => X => Y
        self._eq_symm = self._prove_eq_symm()         # X = Y => Y = X

        self._env.add_impl_rule("to_impl", self._eq_to_impl)
        self._env.add_impl_rule("symm", self._eq_symm)

        self._extensionality = dict() # (var : TermConstant, parindex : int) -> Theorem

    def _build_rw_term(self, term, position):
        subterms = []
        for i in position:
            subterms.append(term)
            term = term.args[i]
        res = BVar(1)
        for term, i in zip(reversed(subterms), reversed(position)):
            args = list(term.args)
            args[i] = res
            res = TermApp(term.f, args, term.bound_names)
        return res

    def add_extensionality(self, theorem):
        env = self._env

        # check assumption, find BODY1, BODY2
        
        assump, main_eq = env.split_impl(theorem.term)
        num_bound = 0
        while assump.f == env.constants.forall:
            [assump] = assump.args
            num_bound += 1
        BODY1_t, BODY2_t = env.split_eq(assump)
        BODY1 = BODY1_t.f
        BODY2 = BODY2_t.f
        assert BODY1.arity == num_bound, (BODY1, BODY1.arity, num_bound)
        assert isinstance(BODY1, TermVariable)
        assert isinstance(BODY2, TermVariable)
        assert BODY1_t.equals_to(BODY1.to_term()), (BODY1_t, BODY1.to_term())
        assert BODY2_t.equals_to(BODY2.to_term()), BODY2_t

        # check main_eq

        a,b = env.split_eq(main_eq)
        constant = a.f
        assert isinstance(constant, TermConstant), constant
        assert constant == b.f, (constant, b.f)
        vs = [x.f for x in a.args]
        assert BODY1 in vs, (BODY1, a)
        index = vs.index(BODY1)
        assert all(
            isinstance(arg.f, TermVariable) and arg.equals_to(arg.f.to_term())
            for i,arg in enumerate(a.args)
            if i != index
        ), a
        assert all(
            v == xb.f
            for i,(v,xb) in enumerate(zip(vs, b.args))
            if i != index
        ), (a,b)
        assert a.args[index].equals_to(BODY1.to_term()), (a.args[index], BODY1)
        assert b.args[index].equals_to(BODY2.to_term()), (b.args[index], BODY2)
        vs_set = set(vs)
        vs_set.add(BODY2)
        assert len(vs_set) == len(vs)+1, vs+[BODY2]

        self._extensionality[constant, index] = theorem, vs, BODY1, BODY2

    def raise_eq(self, eq, body_term, position = None):
        if position is not None:
            body_term = self._build_rw_term(body_term, position)
        if isinstance(body_term, BVar): return eq
        X,Y = self._env.split_eq(eq.term)
        res = self._eq_cong_eq
        res = res.specialize({ self._X : X, self._Y : Y, self._BODY : body_term })
        res = res.modus_ponens_basic(eq)
        return res

    def raise_eq_to_impl(self, eq, pred_term, position = None):
        if position is not None:
            pred_term = self._build_rw_term(pred_term, position)
        X, Y = self._env.split_eq(eq.term)
        if isinstance(pred_term, BVar):
            thm = self._eq_to_impl
            thm = thm.specialize({ self._X : X, self._Y : Y })
        else:
            thm = self._eq_cong
            thm = thm.specialize({ self._X : X, self._Y : Y, self._PRED : pred_term })
        thm = thm.modus_ponens_basic(eq)
        return thm

    def to_root_rewriter(self, *args):
        consts = []
        rw_list = []
        for arg in args:
            if isinstance(arg, RootRewriter):
                cur_rw = arg
            elif isinstance(arg, PatternLookupRewrite):
                cur_rw = RootRewriterPattern(arg)
            elif isinstance(arg, Theorem):
                cur_rw = RootRewriterSingle(arg)
            elif isinstance(arg, (tuple, list)):
                cur_rw = self.to_root_rewriter(*arg)
            elif isinstance(arg, Calculator):
                cur_rw = RootRewriterCalc(self._env, arg)
            elif isinstance(arg, TermConstant):
                consts.append(arg)
                cur_rw = None
            else:
                raise Exception(f"Cannot convert type {type(arg)} to a RootRewriter")
            if cur_rw is not None:
                if consts:
                    rw_list.append(RootRewriterUnfold(self._env, consts))
                    consts = []
                rw_list.append(cur_rw)
        if consts:
            rw_list.append(RootRewriterUnfold(self._env, consts))
        if len(rw_list) == 1:
            return rw_list[0]
        else:
            return RootRewriterList(rw_list)

    def _run_on_arg(self, const, index, args, bound_names, rule, repeat):
        arg = args[index]
        local_vars = []
        extensionality = self._extensionality.get((const,index), None)
        if extensionality is None and const.signature[index]:
            print(f"Warning: missing extensionality theorem for {const}, {index}")
            return None
        if extensionality is not None:
            local_vars = [
                TermVariable(0, name = name.upper())
                for name in bound_names[index]
            ]
            arg = arg.substitute_bvars((
                v.to_term() for v in local_vars
            ))
        arg, arg_eq_rwt = self._run_aux(arg, rule, repeat)
        if arg_eq_rwt is None: return None
        arg_eq, rwt = arg_eq_rwt
        if extensionality is not None:
            eq_vars = arg_eq.free_vars
            if True or any(v in eq_vars for v in local_vars):
                env = self._env
                arg_eq = self.raise_eq(arg_eq, rwt)
                ext_thm, ext_vs, BODY1, BODY2 = extensionality
                subst = {
                    v : arg
                    for v, arg in zip(ext_vs, args)
                }
                arg_eq = arg_eq.generalize(*local_vars, fix_bnames = False)
                t = arg_eq.term
                for _ in range(BODY1.arity): t = t.args[0]
                BODY1_term, BODY2_term = env.split_eq(t)
                subst[BODY1] = BODY1_term
                subst[BODY2] = BODY2_term
                ext_thm_spec = ext_thm.specialize(subst)
                arg_eq = ext_thm_spec.modus_ponens_basic(arg_eq)
                arg_eq_lhs, arg_eq_rhs = env.split_eq(arg_eq.term)
                bn1 = arg_eq_lhs.bound_names
                bn2 = arg_eq_rhs.bound_names
                if bn1 != bound_names or bn2 != bound_names:
                    bnames_correction = TermApp(
                        env.core.equality, (
                            TermApp(const, arg_eq_lhs.args, bound_names),
                            TermApp(const, arg_eq_rhs.args, bound_names),
                        )
                    )
                    arg_eq = arg_eq.alpha_equiv_exchange(bnames_correction)
                rwt = BVar(1)
                arg = arg_eq.term.args[1].args[index]
            else: # TODO: probably doesn't work this way
                rwt = rwt.substitute_bvars([BVar(len(local_vars)+1)])
                subst = {
                    v : BVar(i)
                    for v,i in zip(local_vars, range(len(local_vars), 0, -1))
                }
                rwt = rwt.substitute_free(subst)
                arg = arg.substitute_free(subst)
        else:
            if const.signature[index] > 0:
                rwt = rwt.substitute_bvars([BVar(const.signature[index]+1)])
            args[index] = rwt
            rwt = TermApp(const, args, bound_names)
        args[index] = arg
        return arg_eq, rwt

    def _run_aux(self, term, rule, repeat): # return term, (None | (eq, rw_term))
        res = None
        root_changed = True
        while True:
            while True: # try to rewrite root
                if term.debruijn_height > 0: break
                root_rule = rule.try_rw(term)
                if root_rule is None: break
                term = root_rule.term.args[1]
                if not repeat:
                    return term, (root_rule, BVar(1))
                root_changed = True
                res = self._combine_output(res, root_rule, BVar(1))
            if not root_changed: break
            args_changed = False
            args = list(term.args)
            for i,arg in enumerate(args):
                term_arg0 = TermApp(term.f, args)
                arg_res = self._run_on_arg(term.f, i, args, term.bound_names, rule, repeat)
                if arg_res is None: continue
                term_arg1 = TermApp(term.f, args)
                res = self._combine_output(res, *arg_res)
                args_changed = True
                if not repeat: break
            if not args_changed: break
            term = TermApp(term.f, args, term.bound_names)
            if not repeat: break

            root_changed = False

        return term, res
    def _combine_output(self, res1, eq2, rwt2):
        if res1 is None: return eq2, rwt2
        eq1, rwt1 = res1
        if not isinstance(rwt1, BVar): eq1 = self.raise_eq(eq1, rwt1)
        rwt2 = TermApp(self._env.core.equality, (eq1.term.args[0], rwt2))
        eq2 = self.raise_eq_to_impl(eq2, rwt2)
        eq = eq2.modus_ponens_basic(eq1)
        return eq, BVar(1)

    def run(self, thm_or_term, *rules,
            position = (),
            repeat = False,
            allow_idle = False):
        rule = self.to_root_rewriter(*rules)
        if isinstance(thm_or_term, Term):
            term = thm_or_term
        else:
            assert isinstance(thm_or_term, Theorem)
            term = thm_or_term.term
        subterms = []
        for i in position:
            subterms.append(term)
            term = term.args[i]

        term, eq =  self._run_aux(term, rule, repeat)  # Main rewrite call

        if eq is None:
            if not allow_idle: return None
            elif isinstance(thm_or_term, Theorem): return thm_or_term
            else: return self._eq_refl.specialize({ self._X, thm_or_term })
        eq, rwt = eq
        for term, i in zip(reversed(subterms), reversed(position)):
            args = list(term.args)
            args[i] = rwt
            rwt = TermApp(term.f, args, term.bound_names)
        if isinstance(thm_or_term, Theorem):
            res = self.raise_eq_to_impl(eq, rwt)
            res = res.modus_ponens_basic(thm_or_term)
            return res
        else:
            return self.raise_eq(eq, rwt)

    # basic equality modifications
        
    def _modify_eq(self, eq, modify_rule):
        X,Y = self._env.split_eq(eq.term)
        res = modify_rule
        res = res.specialize({ self._X : X, self._Y : Y })
        res = res.modus_ponens_basic(eq)
        return res
    def eq_to_impl(self, eq):
        return self._modify_eq(eq, self._eq_to_impl)
    def eq_to_rimpl(self, eq):
        return self._modify_eq(eq, self._eq_to_rimpl)
    def eq_symm(self, eq):
        return self._modify_eq(eq, self._eq_symm)

    # checking & proving theorems
    
    def _check_eq_cong(self, eq_cong): # X = Y => PRED(X) => PRED(Y)
        env = self._env
        term = eq_cong.term
        X_eq_Y, term = env.split_impl(term)
        PRED_X, PRED_Y = env.split_impl(term)
        X, Y = env.split_eq(X_eq_Y)
        X = X.f
        Y = Y.f
        PRED = PRED_X.f
        assert isinstance(X, TermVariable)
        assert X.arity == 0
        assert isinstance(Y, TermVariable)
        assert Y.arity == 0
        assert X != Y
        assert isinstance(PRED, TermVariable)
        assert PRED.arity == 1
        assert PRED_X.args[0].f == X
        assert PRED_Y.args[0].f == Y

        # store variables, theorems        

        self._X = X
        self._Y = Y
        self._PRED = PRED

        return eq_cong

    def _check_eq_refl(self, eq_refl): # X = X
        env = self._env
        X, X2 = env.split_eq(eq_refl.term)
        assert X2.f == X.f
        X = X.f
        assert isinstance(X, TermVariable) and X.arity == 0
        if X != self._X:
            eq_refl = eq_refl.specialize({ X : self_X })
        return eq_refl

    def _prove_eq_to_impl(self): # X = Y => X => Y
        return self._eq_cong.specialize({ self._PRED : BVar(1) })

    def _prove_eq_cong_eq(self): # X = Y => BODY(X) = BODY(Y)
        self._BODY = self._env.parser.get_var("BODY", 1)

        # BODY = ( y : PRED(X) = PRED(y) )
        BODY_X = TermApp(self._BODY, (TermApp(self._X),))
        BODY_y = TermApp(self._BODY, (BVar(1),))
        pred_term = TermApp(self._env.core.equality, (BODY_X, BODY_y))
        thm = self._eq_cong
        thm = thm.specialize({ self._PRED : pred_term })
        label = AssumptionLabel("_XY_")
        thm = thm.impl_to_labels(label)
        refl = self._eq_refl
        refl = refl.specialize({ self._X : BODY_X })
        thm = thm.modus_ponens_basic(refl)
        thm = thm.labels_to_impl(label)
        return thm

    def _prove_eq_to_rimpl(self): # X = Y => Y => X
        env = self._env
        label = AssumptionLabel("_XY_")
        X_eq_Y = env.hypothesis(label, self._eq_cong.term.args[0])
        X_to_X = env.basic_impl.refl(self._X.to_term())
        Y_to_X = self.run(X_to_X, X_eq_Y,
                          position = [0], repeat = False)
        res = Y_to_X.labels_to_impl(label)
        res = res.unfreeze()
        return res        

    def _prove_eq_symm(self): # X = Y => Y = X
        env = self._env
        label = AssumptionLabel("_XY_")
        X_eq_Y = env.hypothesis(label, self._eq_cong.term.args[0])
        X_eq_X = self._eq_refl
        Y_eq_X = self.run(X_eq_X, X_eq_Y,
                          position = [0], repeat = False)
        res = Y_eq_X.labels_to_impl(label)
        res = res.unfreeze()
        return res
