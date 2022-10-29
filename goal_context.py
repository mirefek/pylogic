import tactics
from term import Term
from goal_tree import GoalTreeNode, GoalTree

class GoalContext:
    def __init__(self, goal_env, node, unfreeze = True):
        self.goal_env = goal_env
        self.tree = GoalTree(node)
        self.unfreeze = unfreeze
        self.last_node = node,0

    def __enter__(self):
        self.prev_goal_ctx = self.goal_env.current_ctx
        self.goal_env.current_ctx = self
    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_tb is not None: return

        self.goal_env.current_ctx = self.prev_goal_ctx
        thm = self.tree.get_proven()
        if thm is None:
            self.tree.print_goals()
            raise Exception("Proof is not finished")
        if self.unfreeze: thm = thm.unfreeze()
        self.goal_env.last_proven = thm

    def apply_tactic(self, tactic, *args, **kwargs):
        node,d = self.tree.first_leaf()
        tactic(self.goal_env.env, node, *args, **kwargs)
        self.last_node = node,d

        cur_hyp = self.get_last_output()
        if cur_hyp is None: return self.goal_env
        else: return cur_hyp

    def get_last_output(self):
        last_node, dl = self.last_node
        if self.tree.get_proven() is None:
            cur_node,dc = self.tree.first_leaf()
        else:
            cur_node,dc = self.tree.root, 0
        last_branch, cur_branch,_ = self.tree.find_common(
            last_node,dl,
            cur_node,dc,
        )
        cur_hyp = [
            x.tactic_output
            for x in cur_branch
            if x.tactic_output is not None
        ]
        cur_hyp.reverse()

        if len(cur_hyp) == 0: return None
        elif len(cur_hyp) == 1: return cur_hyp[0]
        else: return cur_hyp

class GoalEnv:
    def __init__(self, env):
        self.env = env
        self.current_ctx = None
        self.last_proven = None

    def goal(self, goal_term, unfreeze = True):
        goal_term = self.env.to_term(goal_term)
        parent = self._current_goal()
        if parent is not None:
            parent,_ = parent
        node = GoalTreeNode(goal_term, parent)
        return GoalContext(self, node, unfreeze = unfreeze)
    def subgoal(self, goal_term = None, unfreeze = True):
        cur, _ = self._current_goal()
        if goal_term is None:
            goal_term = cur.term
        else:
            goal_term = self.env.to_term(goal_term)
        if not goal_term.equals_to(cur.term):
            print("Current", cur)
            print("Claimed ", goal_term)
            raise Exception("Subgoal does not match the current goal")
        return GoalContext(self, cur, unfreeze = unfreeze)

    def get_last_output(self):
        return self.current_ctx.get_last_output()
    def _current_goal(self):
        ctx = self.current_ctx
        if not ctx: return None
        return self.current_ctx.tree.first_leaf()

    def __getattr__(self, name):
        if name == "current_goal":
            return self._current_goal()[0]

        tactic = self.env.tactics.get_tactic(name)
        if tactic is None: raise AttributeError(f"No tactic named '{name}'")
        ctx = self.current_ctx
        if ctx is None:
            raise Exception("Cannot apply tactics without a goal context")
        def run(*args, **kwargs):
            return self.current_ctx.apply_tactic(tactic, *args, **kwargs)
        return run
