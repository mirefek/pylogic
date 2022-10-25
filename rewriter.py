from term import Term, TermFunction
from logic_core import AssumptionLabel
from pattern_lookup import PatternLookupRewrite
from pytheorem import Theorem
from unification import Unification

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
            pattern = pattern.union(rw)
        return pattern

class RootRewriterUnfold(RootRewriter):
    def __init__(self, env, consts):
        self.env = env
        self.c_to_def = {
            c : self.env.definitions.get(c, None)
            for c in consts
        }
        assert None not in self.c_to_def.values()
    def try_rw(self, term):
        definition = self.c_to_def.get(term.f, None)
        if definition is None: return None
        A,B = self.env.split_eq(definition.term)
        subst = {
            A_arg.f : term_arg
            for A_arg, term_arg in zip(A.args, term.args)
        }
        return definition.specialize(subst)

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

    def _build_rw_term(self, term, position):
        subterms = []
        for i in position:
            subterms.append(term)
            term = term.args[i]
        res = Term(1)
        for term, i in zip(reversed(subterms), reversed(position)):
            args = list(term.args)
            args[i] = res
            res = Term(term.f, args, term.bound_names)
        return res

    def raise_eq(self, eq, body_term, position = None):
        if position is not None:
            body_term = self._build_rw_term(body_term, position)
        if body_term.is_bvar: return eq
        X,Y = self._env.split_eq(eq.term)
        res = self._eq_cong_eq
        res = res.specialize({ self._X : X, self._Y : Y, self._BODY : body_term })
        res = res.modus_ponens_basic(eq)
        return res

    def raise_eq_to_impl(self, eq, pred_term, position = None):
        if position is not None:
            pred_term = self._build_rw_term(pred_term, position)
        X, Y = self._env.split_eq(eq.term)
        if pred_term.is_bvar:
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
                cur_rw = self.to_root_rewriter(*args)
            elif isinstance(arg, TermFunction):
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

    def _run_aux(self, term, rule, repeat): # return term, (None | (eq, rw_term))
        res = None
        root_changed = True
        while True:
            while True: # try to rewrite root
                root_rule = rule.try_rw(term)
                if root_rule is None: break
                term = root_rule.term.args[1]
                if not repeat:
                    return term, (root_rule, Term(1))
                root_changed = True
                res = self._combine_output(res, root_rule, Term(1))
            if not root_changed: break
            args_changed = False
            args = list(term.args)
            for i,arg in enumerate(args):
                arg, arg_eq = self._run_aux(arg, rule, repeat)
                if arg_eq is None: continue
                eq, rwt = arg_eq
                args[i] = rwt
                rwt = Term(term.f, args, term.bound_names)
                res = self._combine_output(res, eq, rwt)
                args[i] = arg
                args_changed = True
                if not repeat: break
            if not args_changed: break
            term = Term(term.f, args, term.bound_names)
            if not repeat: break

            root_changed = False
        return term, res
    def _combine_output(self, res1, eq2, rwt2):
        if res1 is None: return eq2, rwt2
        eq1, rwt1 = res1
        if not rwt1.is_bvar: eq1 = self.raise_eq(eq1, rwt1)
        rwt2 = Term(self._env.core.equality, (eq1.term.args[0], rwt2))
        eq2 = self.raise_eq_to_impl(eq2, rwt2)
        eq = eq2.modus_ponens_basic(eq1)
        return eq, Term(1)

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
            elif isinstance(thm_or_eq, Theorem): return thm_or_eq
            else: return self._eq_refl.specialize({ self._X, thm_or_term })
        eq, rwt = eq
        for term, i in zip(reversed(subterms), reversed(position)):
            args = list(term.args)
            args[i] = rwt
            rwt = Term(term.f, args, term.bound_names)
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
        assert X.is_free_variable
        assert X.arity == 0
        assert Y.is_free_variable
        assert Y.arity == 0
        assert X != Y
        assert PRED.is_free_variable
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
        assert X.is_free_variable and X.arity == 0
        if X != self._X:
            eq_refl = eq_refl.specialize({ X : self_X })
        return eq_refl

    def _prove_eq_to_impl(self): # X = Y => X => Y
        return self._eq_cong.specialize({ self._PRED : Term(1) })

    def _prove_eq_cong_eq(self): # X = Y => BODY(X) = BODY(Y)
        self._BODY = self._env.parser.get_var("BODY", 1)

        # BODY = ( y : PRED(X) = PRED(y) )
        BODY_X = Term(self._BODY, (Term(self._X),))
        BODY_y = Term(self._BODY, (Term(1),))
        pred_term = Term(self._env.core.equality, (BODY_X, BODY_y))
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
