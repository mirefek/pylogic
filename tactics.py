from logic_core import AssumptionLabel
from unification import Unification
from pattern_lookup import PatternLookup
from pytheorem import Theorem
from goal_tree import GoalTreeNode

class Tactics:
    def __init__(self, env):
        self._env = env
        self._tactics = dict()

        self.register("intros", Intros)
        self.register("intro", lambda env, goal, : Intros(env, goal, 1))
        self.register("exact", lambda env, goal, thm : ApplyExact(env, goal, thm, 0))
        self.register("app_exact", ApplyExact)
        self.register("app", apply_spec)
        self.register("rw", rewrite_goal)
        self.register("postpone", Postpone)
        self.register("assumed", assumed)

    def register(self, name, tactic, num_subgoals = None):
        assert isinstance(name, str)
        if isinstance(tactic, Theorem):
            pattern = self._tactics.get(name, None)
            if pattern is None:
                pattern = PatternLookupGoal()
            assert isinstance(pattern, PatternLookupGoal)
            self._tactics[name] = pattern.add_rule(tactic, num_subgoals)
        else:
            assert num_subgoals is None
            assert name not in self._tactics
            self._tactics[name] = tactic

    def get_tactic(self, name):
        return self._tactics.get(name, None)

class BasicTactic:
    def __init__(self, env, node, *args, **kwargs): # Goal -> list[Goal] + set self.output
        self.node = node
        self.env = env
        self.goal = node.term
        self.outputs = None
        subgoals = self.get_subgoals(*args, **kwargs)
        if self.outputs is not None:
            assert len(self.outputs) == len(subgoals)
            outputs = self.outputs
        else:
            outputs = [None]*len(subgoals)
        node.tactic = self
        node.children = [
            GoalTreeNode(subgoal, node, tactic_output = output)
            for subgoal, output in zip(subgoals, outputs)
        ]
        node.check_closed()
    def get_subgoals(self, *args, **kwargs):
        raise Exception("Not implemented")
    def build_thm(self, *thms): # list[Theorem] -> Theorem
        raise Exception("Not implemented")

class Intros(BasicTactic):
    def get_subgoals(self, *labels):
        if len(labels) == 1 and isinstance(labels[0], int):
            labels = (None,)*labels[0]
        elif len(labels) == 1 and isinstance(labels[0], (tuple, list)):
            [labels] = labels

        aterms = []
        term = self.goal
        if not labels:
            labels = []
            while term.f == self.env.core.implication:
                aterm, term = term.args
                labels.append(None)
                aterms.append(aterm)
            if len(labels) == 0:
                raise Exception(f"Intro failed: not an implication: {term}")
        else:
            labels = list(labels)
            for _ in labels:
                if term.f != self.env.core.implication:
                    raise Exception(f"Intro failed: not an implication: {term}")
                aterm, term = term.args
                aterms.append(aterm)

        for i,label in enumerate(labels):
            if label is None: label = "_HYP_"
            if isinstance(label, str): label = AssumptionLabel(label)
            assert isinstance(label, AssumptionLabel)
            labels[i] = label

        self.assumptions = tuple(
            self.env.hypothesis(label, aterm)
            for label, aterm in zip(labels, aterms)
        )
        if len(self.assumptions) == 1:
            self.outputs = [self.assumptions[0]]
        else:
            self.outputs = [self.assumptions]

        self.labels = labels
        self.aterms = aterms
        return [term]

    def build_thm(self, thm):
        thm_labels = thm.assump_labels()
        for label, aterm in zip(self.labels, self.aterms):
            if label not in thm_labels:
                thm = self.env.basic_impl.add(thm, aterm, label)
        thm = thm.labels_to_impl(self.labels)
        return thm

class ApplyExact(BasicTactic):
    def get_subgoals(self, thm, num_subgoals):
        aterms = []
        term = thm.term
        for _ in range(num_subgoals):
            aterm, term = self.env.split_impl(term)
            aterms.append(aterm)

        if not term.equals_to(self.goal):
            raise Exception(f"Exact term {thm.term} doesn't fit the goal {self.goal}")
        self.thm = thm
        self.subgoals = tuple(aterms)
        return self.subgoals
    def build_thm(self, *subthms):
        thm = self.thm
        for subthm in subthms:
            thm = thm.modus_ponens_basic(subthm)
        return thm

def apply_spec(env, node, thm, num_subgoals = None):
    goal = node.term
    aterms = []
    term = thm.term
    while (len(aterms) != num_subgoals and term.f == env.core.implication):
        aterm, term = term.args
        aterms.append(aterm)
    assert num_subgoals in (None, len(aterms))
    num_subgoals = len(aterms)

    unification = Unification((thm.frozen_vars, None))
    unification.add_requirement(term,0, goal,1)
    if not unification.run():
        unification.print_requirements()
        raise Exception(f"Apply: Unification failed: {thm.term} WITH {goal}")
    subst, _ = unification.export_substitutions(
        [thm.free_vars, goal.free_vars],
        None, # metavariables are not supported (yet?)
    )
    return ApplyExact(env, node, thm.specialize(subst), num_subgoals)

def rewrite_goal(env, node, *rules, **rw_kwargs):
    eq = env.rewriter.run(node.term, *rules, **rw_kwargs)
    if eq is None:
        raise Exception(f"Nothing to rewrite in {node.term}")
    rimpl = env.rewriter.eq_to_rimpl(eq)
    ApplyExact(env, node, rimpl, 1)

class Postpone(BasicTactic):
    def get_subgoals(self, label, frozen = False):
        self.thm = self.env.hypothesis(label, self.goal, frozen = frozen)
        return []
    def build_thm(self):
        return self.thm

class PatternLookupGoal(PatternLookup):
    def add_rule(self, thm, num_subgoals = None):
        env = thm._env
        n = 0
        term = thm.term
        while n != num_subgoals and term.f == env.core.implication:
            term = term.args[1]
            n += 1
        assert num_subgoals in (None, n)
        return self.add_pattern(term, (thm, n))

    def final_step(self, term, match_term, thm_n):
        thm, num_subgoals = thm_n
        subst = self._final_unify(term, match_term, thm.free_vars)
        if subst is None: return None
        thm = thm.specialize(subst)
        return thm, num_subgoals

    def __call__(self, env, node):
        thm_n = self.find_first(node.term)
        if thm_n == None:
            raise Exception(f"Failed to apply tactic pattern: {node.term}")
        thm, num_subgoals = thm_n
        return ApplyExact(env, node, thm, num_subgoals)

def assumed(env, node):
    n = node
    for assump in node.assumptions():
        if assump.term.equals_to(node.term):
            ApplyExact(env, node, assump, 0)
            return

    raise Exception("Goal {node.term} not found among assumptions")
    
