from logic_core import AssumptionLabel

# proving basic implications

class BasicImpl:
    def __init__(self, add_assump): # X -> A -> X
        self.env = add_assump._env
        self.prepare_add_assump(add_assump)
        self.prepare_impl_refl()

    def prepare_add_assump(self, thm):
        term = thm.term
        X, res = self.env.split_impl(term)
        assert X.f.is_free_variable and X.f.arity == 0
        A, X2 = self.env.split_impl(res)
        assert A.f.is_free_variable and A.f.arity == 0
        assert A.f != X.f, A
        assert X2.f == X.f, X2
        self._X = X
        self._A = A
        self._add_assump = thm
    def add(self, thm, term, label = None):
        term = self.env.to_term(term)
        x = self._add_assump
        x = x.specialize({
            self._X.f : thm.term,
            self._A.f : term
        })
        x = x.modus_ponens_basic(thm)
        if label is not None:
            label = self.env.to_label(label)
            assert isinstance(label, AssumptionLabel)
            x = x.impl_to_labels_basic(label)
        return x

    def prepare_impl_refl(self):
        label = AssumptionLabel("HYP")
        x = self._add_assump
        x = x.specialize({self._A.f : self._X})
        x = x.impl_to_labels(label, label)
        x = x.labels_to_impl(label)
        self._impl_refl = x
    def refl(self, term):
        return self._impl_refl.specialize({ self._X.f : term })
