from term import Term, TermApp, TermFunction

class AssumptionRearrangement:
    def __init__(self, logic, basic_nmp, basic_ada):
        self.logic = logic
        self._assumption_vars = []
        self._X = TermApp(TermFunction((), True, "_X"))
        self._Y = TermApp(TermFunction((), True, "_Y"))
        self._nmps = [ # (... => (X => Y)) => (... => X) => (... => Y)
            self._prepare_basic_nmp(basic_nmp)
        ]
        self._adas = [[ # (... => X) => (... => (... => X))
            self._prepare_basic_ada(basic_ada)
        ]]
        self._rchains = [] # (... => X => Y) => (... => Ai => X) => (.. => Ai => Y)
        self._impl_refl = None
        self._shifts = []

    def impl_refl(self, X):
        return self.logic.specialize(self._get_impl_refl(), { self._X.f : X })

    def add_assump(self, thm, assumptions, depth = 0):
        num_added = len(assumptions)
        if num_added == 0: return thm
        local_thm = thm
        all_assump = []
        for _ in range(depth):
            x, local_thm = self._split_impl(local_thm)
            all_assump.append(x)
        all_assump.extend(assumptions)
        d = {
            self._A(i).f : assump
            for i,assump in enumerate(all_assump)
        }
        d[self._X.f] = local_thm
        return self._add_assump(thm, depth, num_added, d)

    def modus_ponens(self, A_to_B, A, depth = 0):
        local_A_to_B = A_to_B
        local_A = A
        assump = []
        d = dict()
        for i in range(depth):
            a, local_A_to_B = self._split_impl(local_A_to_B)
            a2, local_A = self._split_impl(local_A)
            d[self._A(i).f] = a
        local_A2, local_B = self._split_impl(local_A_to_B)
        d[self._X.f] = local_A
        d[self._Y.f] = local_B
        return self._modus_ponens(A_to_B, A, depth, d)

    def chain(self, A_to_B, B_to_C, depth = 0):
        local_A_to_B = A_to_B
        local_B_to_C = B_to_C
        d = dict()
        for i in range(depth):
            a, local_A_to_B = self._split_impl(local_A_to_B)
            a2, local_B_to_C = self._split_impl(local_A_to_B)
            d[self._A(i).f] = a
        A,B = self._split_impl(local_A_to_B)
        B2,C = self._split_impl(local_B_to_C)
        d[self._A(depth).f] = A
        d[self._X.f] = B
        d[self._Y.f] = C
        return self._rchain(B_to_C, A_to_B, depth, d)

    def shift(self, thm, depth, num_to_skip):
        assert num_to_skip >= 0
        if num_to_skip == 0: return thm
        local_thm = thm
        d = dict()
        for i in range(depth):
            a, local_thm = self._split_impl(local_thm)
            d[self._A(i).f] = a
        X, local_thm = self._split_impl(local_thm)
        d[self._X.f] = X
        for i in range(num_to_skip):
            a, local_thm = self._split_impl(local_thm)
            d[self._A(depth+i).f] = a
        d[self._Y.f] = local_thm
        return self._shift_assump(thm, d)

    def _A(self, i):
        while i >= len(self._assumption_vars):
            self._assumption_vars.append(
                TermApp(TermFunction((), True, f"_A{len(self._assumption_vars)}"))
            )
        return self._assumption_vars[i]

    def _modus_ponens(self, A_to_B, A, depth, assignment_d):
        if depth == 0:
            return self.logic.modus_ponens(impl, assump)
        x = self._get_nmp(depth)
        x = self.logic.specialize(x, assignment_d)
        x = self.logic.modus_ponens(x, A_to_B)
        x = self.logic.modus_ponens(x, A)
        return x
    def _add_assump(self, thm, depth, num_added, assignment_d):
        if num_added == 0: return thm
        x = self._get_ada(depth, num_added)
        x = self.logic.specialize(x, assignment_d)
        x = self.logic.modus_ponens(x, thm)
        return x
    def _rchain(self, B_to_C, A_to_B, depth, assignment_d):
        x = self._get_rchain(depth)
        x = self.logic.specialize(x, assignment_d)
        x = self.logic.modus_ponens(x, B_to_C)
        x = self.logic.modus_ponens(x, A_to_B)
        return x
    def _shift(self, thm, depth, num_to_skip, assignment_d):
        if num_to_skip == 0: return thm
        x = self._get_shift(depth, num_to_skip)
        x = self.logic.specialize(x, assignment_d)
        x = self.logic.modus_ponens(thm)
        return x

    def _get_ada(self, depth, num_added):
        assert depth >= 0 and num_added > 0
        while len(self._adas) <= depth: self._adas.append([])
        d_ada = self._adas[depth]
        while len(d_ada) <= (num_added-1): d_ada.append(None)
        res = d_ada[num_added-1]
        if res is None:
            res = self._construct_ada(depth, num_added)
            d_ada[num_added-1] = res
        return res
    def _construct_ada(self, depth, num_added):
        if num_added == 1:
            x = self._get_ada(0,1) # X => A => X
            x = self.logic.specialize(  # X => (Ai => X)
                x, {self._A(0).f : self._A(depth)})
            x = self._add_assump(x, 0, depth, { # ...=> (X => (Ai => X))
                self._X.f : x
            })
            m = self._get_nmp(depth)
            m = self.logic.specialize(m, {
                self._Y.f : self._impl(self._A(depth), self._X)
            })
            return self.logic.modus_ponens(m, x)
        else:
            return self.chain(
                self._get_ada(depth, num_added-1),
                self._get_ada(depth+num_added-1, 1),
            )

    def _get_nmp(self, depth):
        assert depth > 0
        while len(self._nmps) <= (depth-1):
            self._nmps.append(self._construct_nmp(len(self._nmps)+1))
        return self._nmps[depth-1]
    def _construct_nmp(self, depth): # depth >= 2
        a = self._get_nmp(1)
        a = self.logic.specialize(a, { self._A(0).f : self._A(depth-1) })
        A_to_X_to_Y = a.args[0]
        A_to_X_to_A_to_Y = a.args[1]
        A_to_X = A_to_X_to_A_to_Y.args[0]
        A_to_Y = A_to_X_to_A_to_Y.args[1]
        a = self._add_assump(a, 0, depth-1, { self._X.f : a })
        # a = ... => (A2 => X => Y) => (A2 => X) => (A2 => Y)
        m = self._get_nmp(depth-1)
        m = self.logic.specialize(m, {
            self._X.f : A_to_X_to_Y,
            self._Y.f : A_to_X_to_A_to_Y,
        })
        a = self.logic.modus_ponens(m, a)
        # a = (... => A2 => X => Y) => (... => ((A2 => X) => (A2 => Y)) )
        b = self._get_nmp(depth-1)
        b = self.logic.specialize(b, {
            self._X.f : A_to_X,
            self._Y.f : A_to_Y,
        })
        # b = (... => (A2 => X) => (A2 => Y)) => (... => A2 => X) => (... => A2 => Y)
        return self.chain(a,b)

    def _get_rchain(self, depth):
        while len(self._rchains) <= depth:
            self._rchains.append(self._construct_rchain(len(self._rchains)))
        return self._rchains[depth]
    def _construct_rchain(self, depth):
        x = self._get_ada(depth, 1) # (... => X) => (... => Ai => X)
        x = self.logic.specialize(x, { # (... => (X => Y)) => (... => Ai => (X => Y))
            self._X.f : self._impl(self._X, self._Y),
        })
        y = self._get_nmp(depth+1)
        if depth > 0:
            return self.chain(x,y)
        else: # manual chaining, again the same idea
            A = x.args[0]
            B = x.args[1]
            C = y.args[1]
            y = self._add_assump(y, 0, 1, {
                self._X.f : y,
                self._A(0).f : A,
            })
            m = self._get_nmp(1)
            m = self.logic.specialize(m, {
                self._A(0).f : A,
                self._X.f : B,
                self._Y.f : C,
            })
            m = self.logic.modus_ponens(m, y)
            m = self.logic.modus_ponens(m, x)
            return m

    def _get_impl_refl(self):
        if self._impl_refl is None:
            self._impl_refl = self._construct_impl_refl()
        return self._impl_refl
    def _construct_impl_refl(self):
        T = self._get_ada(0,1)
        a = self._add_assump(T, 0,1, { # X => T
            self._X.f : T,
            self._A(0).f : self._X,
        })
        b = self._get_ada(0,1)
        b = self.logic.specialize(b, { # X => T => X
            self._A(0).f : T
        })
        b = self._modus_ponens(b,a,1,{
            self._A(0).f : self._X,
            self._X.f : T,
            self._Y.f : self._X,
        })
        return b

    def _get_shift(self, depth, num_skip):
        assert depth >= 0 and num_skip > 0
        while len(self._shifts) <= depth:
            self._shifts.append([])
        d_shifts = self._shifts[depth]
        while len(d_shifts) <= num_skip-1: d_shifts.append(None)
        res = d_shifts[num_skip-1]
        if res is None:
            res = self._construct_shift(depth, num_skip)
            d_shifts[num_skip-1] = res
        return res
    def _construct_shift(self, depth, num_skip):
        if num_skip > 1:
            a = self._get_shift(depth, num_skip-1)
            a = self.logic.specialize(a, {
                self._Y.f : self._impl(self._A(depth+num_skip-1), self._Y)
            })
            b = self._get_shift(depth+num_skip-1, 1)
            return self.chain(a,b)
        elif depth > 0:
            a = self._get_shift(0, 1)
            a = self.logic.specialize(a, { self._A(0).f : self._A(depth) })
            X_to_Ai_to_Y = a.args[0]
            X_to_Y_to_Ai = a.args[1]
            a = self._add_assump(a,0,depth, { self._X.f : a })
            # a = ... => (X => Ai => Y) => (Ai => X => Y)
            m = self._get_nmp(depth)
            m = self.logic.specialize(m, {
                self._X.f : X_to_Ai_to_Y,
                self._Y.f : X_to_Y_to_Ai,
            })
            a = self.logic.modus_ponens(m,a)
            # a = (... => X => Ai => Y) => (... => Ai => X => Y)
            return a
        else:
            A = self._A(0)
            X = self._X
            Y = self._Y
            X_to_A_to_Y = self._impl(X, self._impl(A, Y))
            assumptions = [X_to_A_to_Y, A, X]
            a = self.impl_refl(X_to_A_to_Y)
            a = self.add_assump(a, assumptions[1:], depth = 1) # X => A => Y
            b = self.impl_refl(A)
            b = self.add_assump(b, assumptions[2:], depth = 1) # A
            b = self.add_assump(b, assumptions[:1])
            c = self.add_assump(self._get_impl_refl(), assumptions[:2]) # X
            x = self.modus_ponens(a,c, depth = 3) # A => Y
            x = self.modus_ponens(x,b, depth = 3) # Y
            return x

    def _impl(self, A, B):
        return TermApp(self.logic.implication, (A, B))

    # checking the right form of basic axioms + renaming their variables

    def _split_impl(self, term):
        assert term.f == logic.implication, term
        return term.args
        assert res.is_free_variable and res.arity == 0, res
    def _prepare_basic_ada(self, basic_ada):
        ori_X, res = self._split_impl(basic_ada)
        assert ori_X.f.is_free_variable and ori_X.f.arity == 0
        ori_A, ori_X2 = self._split_impl(res)
        assert ori_A.f.is_free_variable and ori_A.f.arity == 0
        assert ori_X2.f == ori_X.f, ori_X2
        return self.logic.specialize(basic_ada, {
            ori_A.f : self._A(0),
            ori_X.f : self._X,
        })
    def _prepare_basic_nmp(self, basic_nmp):
        assump1, res = self._split_impl(basic_nmp)
        assump2, res = self._split_impl(res)
        ori_A, assump1_res = self._split_impl(assump1)
        assert ori_A.f.is_free_variable and ori_A.f.arity == 0
        ori_X, ori_Y = self._split_impl(assump1_res)
        assert ori_X.f.is_free_variable and ori_X.f.arity == 0
        assert ori_Y.f.is_free_variable and ori_Y.f.arity == 0
        assert ori_A.f != ori_X.f
        assert ori_A.f != ori_Y.f
        assert ori_X.f != ori_Y.f
        ori_A2, ori_X2 = self._split_impl(assump2)
        assert ori_A2.f == ori_A.f, ori_A2
        assert ori_X2.f == ori_X.f, ori_X2
        ori_A2, ori_Y2 = self._split_impl(res)
        assert ori_A2.f == ori_A.f, ori_A2
        assert ori_Y2.f == ori_Y.f, ori_Y2
        return self.logic.specialize(basic_nmp, {
            ori_A.f : self._A(0),
            ori_X.f : self._X,
            ori_Y.f : self._Y,
        })

if __name__ == "__main__":
    from logic_core import LogicCore
    from parse_term import TermParser

    logic = LogicCore()
    parser = TermParser(logic)
    parser.parse_file("axioms_logic")
    ara = AssumptionRearrangement(
        logic,
        parser.name_to_axiom["nested_modus_ponens"],
        parser.name_to_axiom["dummy_assump"],
    )
    print('|', ara._construct_shift(3,2))
