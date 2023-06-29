from term import Term, TermApp, BVar, TermVariable, TermConstant

class Proof:
    pass

class ProofAxiom(Proof):
    def __init__(self, data):
        self.data = data
class ProofDefinition(Proof):
    def __init__(self, defined_constant):
        self.defined_constant = defined_constant

class ProofModusPonens(Proof):
    def __init__(self, impl, assump):
        self.impl = impl
        self.assump = assump
class ProofSpecialize(Proof):
    def __init__(self, thm, subst):
        self.thm = thm
        self.subst = subst
class ProofRelabel(Proof):
    def __init__(self, thm, label_subst):
        self.thm = thm
        self.label_subst = label_subst
class ProofImplToLabels(Proof):
    def __init__(self, thm, labels):
        self.thm = thm
        self.labels = labels
class ProofLabelsToImpl(Proof):
    def __init__(self, thm, labels):
        self.thm = thm
        self.labels = labels

class AssumptionLabel:
    def __init__(self, name="?label"):
        self.name = name

class DefinedConstant(TermConstant):
    def __init__(self, signature, name):
        super().__init__(signature, name)
        self.def_thm = None
        self.def_core_thm = None # to be set

class CoreTheorem:
    def __init__(self, core, assumptions, term, proof, age, free_vars = None):
        if not isinstance(core, LogicCore):
            raise Exception("Trying to create a core theorem without a logic core")
        if not core._creating_theorem:
            raise Exception("Core theorem can be only built using a logic core")
        self._age = age
        self._core = core
        self._assumptions = assumptions
        self._term = term
        self._proof = proof
        if free_vars is None:
            free_vars = set(self._term.free_vars)
            for aterm in assumptions.values():
                free_vars.update(aterm.free_vars)
        self._free_vars = frozenset(free_vars)

    @property
    def age(self): return self._age
    @property
    def term(self): return self._term
    @property
    def proof(self): return self._proof
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
        proof = ProofModusPonens(self, other)
        return self._core._make_thm(assumptions, term, proof)

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
        proof = ProofSpecialize(self, tuple(subst.items()))
        return self._core._make_thm(assumptions, term, proof)

    def relabel(self, label_subst):
        for label, label_new in label_subst.items():
            assert isinstance(label, AssumptionLabel)
            assert isinstance(label_new, AssumptionLabel)
        assumptions = dict()
        for label, aterm in self.assump_items():
            label_new = label_subst.get(label, label)
            self._add_to_assumptions(assumptions, label_new, aterm)
        term = self._term
        proof = ProofRelabel(self, tuple(label_subst.items()))
        return self._core._make_thm(assumptions, term, proof, self._free_vars)

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
        proof = ProofImplToLabels(self, tuple(labels))
        return self._core._make_thm(assumptions, term, proof, self._free_vars)

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
        proof = ProofLabelsToImpl(self, tuple(labels))
        return self._core._make_thm(assumptions, term, proof, self._free_vars)

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
        self._last_age = 0

    def _make_thm(self, assumptions, term, proof, free_vars = None):
        self._creating_theorem = True
        if not self._record_proof: proof = None
        self._last_age += 1
        thm = CoreTheorem(self, assumptions, term, proof, self._last_age, free_vars)
        self._creating_theorem = False
        return thm

    @property
    def last_age(self):
        return self._last_age

    def add_axiom(self, axiom, axiom_data):
        if self._strict_mode:
            raise Exception("Cannot add axioms in strict mode")
        assert isinstance(axiom, Term)
        assert axiom.is_closed
        proof = ProofAxiom(axiom_data)
        return self._make_thm(dict(), axiom, proof)

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
        proof = ProofDefinition(f)
        thm = self._make_thm(dict(), def_term, proof, frozenset(var_set))
        f.def_core_thm = thm
        return f

class Verifier:
    def __init__(self, core):
        self.core = core
        core.add_trusted_verifier(self)
    def _make_thm(self, assumptions, term, proof):
        core = self.core
        assert self in core._trusted
        return self.core._make_thm(assumptions, term, proof)
