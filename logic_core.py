from term import Term, TermApp, BVar, TermVariable, TermConstant

class AssumptionLabel:
    def __init__(self, name="?label"):
        self.name = name

class DefinedConstant(TermConstant):
    def __init__(self, signature, name):
        super().__init__(signature, name)
        self.def_thm = None
        self.def_core_thm = None # to be set

class CoreTheorem:
    def __init__(self, core, assumptions, term, origin, free_vars = None):
        if not isinstance(core, LogicCore):
            raise Exception("Trying to create a core theorem without a logic core")
        if not core._creating_theorem:
            raise Exception("Core theorem can be only built using a logic core")
        self._core = core
        self._assumptions = assumptions
        self._term = term
        self._origin = origin
        if free_vars is None:
            free_vars = set(self._term.free_vars)
            for aterm in assumptions.values():
                free_vars.update(aterm.free_vars)
        self._free_vars = frozenset(free_vars)

    @property
    def term(self): return self._term
    @property
    def origin(self): return self._origin
    @property
    def free_vars(self): return self._free_vars
    @property
    def has_assumptions(self): return bool(self._assumptions)

    def assumption(self, label): return self._assumptions.get(label, None)
    def assump_items(self): return self._assumptions.items()
    def assump_labels(self): return self._assumptions.keys()
    def assumptions(self): return self._assumptions.values()

    @staticmethod
    def _add_to_assumptions(assumptions, label, term):
        ori = assumptions.setdefault(label, term)
        if ori is not term and not ori.equals_to(term):
            print("Label:", label.name)
            print("Term1:", ori)
            print("Term2: ", term)
            raise Exception("Equally labelled assumptions not fitting")

    def modus_ponens(self, other):
        assert self._core is other._core
        if self._term.f != self._core.implication:
            print("Implication:", self._term)
            raise Exception("Implication statement is not of an implication form")
        if not self._term.args[0].equals_to(other._term):
            print("Implication:", self._term)
            print("Issumption:", self._term.args[0])
            print("Assumption:", other._term)
            raise Exception("Assumption doesn't fit the implication")

        if not other.has_assumptions: assumptions = self._assumptions
        elif not self.has_assumptions: assumptions = other._assumptions
        elif self._assumptions == other._assumptions:
            assumptions = self._assumptions
        else:
            assumptions = dict(self._assumptions)
            for label, aterm in other.assump_items():
                self._add_to_assumptions(assumptions, label, aterm)
        term = self._term.args[1]
        origin = "modus_ponens", self, other
        return self._core._make_thm(assumptions, term, origin)

    def specialize(self, subst):
        for v,t in subst.items():
            assert isinstance(v, TermVariable)
            if not (t.debruijn_height <= v.arity):
                print()
                print(self)
                print(v, ":= ", t)
                raise Exception("Cannot substitute a term with variables bound above")
        assumptions = {
            label : aterm.substitute_free(subst)
            for label, aterm in self.assump_items()
        }
        if assumptions == self._assumptions:
            assumptions = self._assumptions
        term = self._term.substitute_free(subst)
        origin = "specialize", tuple(subst.items())
        return self._core._make_thm(assumptions, term, origin)

    def relabel(self, label_subst):
        for label, label_new in label_subst.items():
            assert isinstance(label, AssumptionLabel)
            assert isinstance(label_new, AssumptionLabel)
        assumptions = dict()
        for label, aterm in self.assump_items():
            label_new = label_subst.get(label, label)
            self._add_to_assumptions(assumptions, label_new, aterm)
        term = self._term
        origin = "relabel", tuple(label_subst.items())
        return self._core._make_thm(assumptions, term, origin, self._free_vars)

    def impl_to_labels(self, *labels):
        assert all(isinstance(label, AssumptionLabel) for label in labels)

        assumptions = dict(self._assumptions)
        term = self._term
        for label in labels:
            if term.f != self._core.implication:
                print("Implication:", self._term)
                raise Exception("Cannot introduce labelled assumption not an implication form")
            aterm = term.args[0]
            term = term.args[1]
            self._add_to_assumptions(assumptions, label, aterm)
        origin = "impl_to_labels", tuple(labels)
        return self._core._make_thm(assumptions, term, origin, self._free_vars)

    def labels_to_impl(self, *labels):
        for label in labels:
            assert isinstance(label, AssumptionLabel)
            if label not in self._assumptions:
                raise Exception(f"Unknown assumption label:", label.name)

        assumptions = dict(self._assumptions)
        for label in set(labels):
            if label in assumptions:
                del assumptions[label]
        term = self._term
        for label in reversed(labels):
            term = TermApp(self._core.implication, (self.assumption(label), term))
        origin = "labels_to_impl", tuple(labels)
        return self._core._make_thm(assumptions, term, origin, self._free_vars)

    def to_str(self):
        res_strs = [
            f"( {label.name} :: {aterm}   ) =>"
            for label, aterm in self.assump_items()
        ]
        res_strs.append("Thm: "+self._term.to_str())
        return '\n'.join(res_strs)
    def __str__(self):
        return self.to_str()

class LogicCore:
    def __init__(self, record_proof = False):
        self._thms = dict() # multiset -- thm to count
        self._strict_mode = False
        self.equality = TermConstant((0,0), name = "__eq__")
        self.implication = TermConstant((0,0), name = "__impl__")
        self._creating_theorem = False
        self._trusted = set()
        self._record_proof = record_proof

    def _make_thm(self, assumptions, term, origin, free_vars = None):
        self._creating_theorem = True
        if not self._record_proof: origin = "unrecorded"
        thm = CoreTheorem(self, assumptions, term, origin, free_vars)
        self._creating_theorem = False
        return thm

    def add_axiom(self, axiom, axiom_data):
        if self._strict_mode:
            raise Exception("Cannot add axioms in strict mode")
        assert isinstance(axiom, Term)
        assert axiom.is_closed
        origin = "axiom", axiom_data
        return self._make_thm(dict(), axiom, origin)

    def add_trusted_verifier(self, verifier):
        self._trusted.add(verifier)

    def add_definition(self, var_list, body, name = None, bound_names = None):
        var_set = set()
        assert isinstance(body, Term)
        assert body.is_closed
        var_list = tuple(var_list)
        for v in var_list:
            assert isinstance(v, TermVariable)
            if v in var_set:
                raise Exception("Variable repetition in definition")
            var_set.add(v)
        if not (body.free_vars <= var_set):
            missing = [str(v.to_term()) for v in body.free_vars-var_set]
            raise Exception(f"var_list doesn't cover all the free variables: {missing}")
        f = DefinedConstant(tuple(v.arity for v in var_list), name = name)
        var_list_t = tuple(
            TermApp(v, tuple(BVar(i) for i in range(v.arity,0,-1)))
            for v in var_list
        )
        def_term = TermApp(
            self.equality,
            (
                TermApp(f, var_list_t, bound_names = bound_names),
                body,
            )
        )
        origin = "definition", f
        thm = self._make_thm(dict(), def_term, origin, frozenset(var_set))
        f.def_core_thm = thm
        return f

class Verifier:
    def __init__(self, core, name = "verifier"):
        self.core = core
        self.name = name
        core.add_trusted_verifier(self)
    def _make_thm(self, assumptions, term, data = None):
        core = self.core
        assert self in core._trusted
        origin = self.name, data
        return self.core._make_thm(assumptions, term, origin)
