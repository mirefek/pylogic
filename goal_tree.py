from term import Term

class GoalTreeNode:
    def __init__(self, term, parent = None, tactic_output = None):
        self.term = term
        self.parent = parent
        self.tactic = None
        self.tactic_output = tactic_output
        self.children = None
        self.closed_with = None

    @property
    def is_closed(self):
        return self.closed_with is not None
    @property
    def is_leaf(self):
        return self.tactic is None

    def check_closed(self):
        x = self
        while x is not None and x.children is not None and all(c.is_closed for c in x.children):
            x.closed_with = x.tactic.build_thm(*(
                c.closed_with for c in x.children
            ))
            x = x.parent

    def __str__(self):
        return "Goal: "+self.term.to_str()

# A structure keeping knowledge about open leafs

class GoalTree:
    def __init__(self, root):
        self.root = root
        self._next_open = {
            None : (root,0),
            root : (None,None),
        }
        self._node_to_depth = {
            root : 0
        }

    def leaf_iter(self):
        x = None
        y,d = self._next_open[None]
        while y is not None:
            if y.is_leaf:
                yield y,d
                x = y
                y,d = self._next_open[y]
            elif y.is_closed:
                y,d = self._next_open.pop(y)
                self._next_open[x] = y,d
            else:
                last = x
                first = None
                for suby in y.children:
                    if suby.is_closed: continue
                    else:
                        if first is None: first = suby
                        self._next_open[last] = suby, d+1
                        last = suby
                self._next_open[last] = self._next_open.pop(y)
                y,d = first,d+1

    def first_leaf(self):
        return next(self.leaf_iter())
    def nth_leaf(self, n):
        it = self.leaf_iter()
        for _ in range(n): next(it)
        return next(it)
    def all_leafs(self):
        return list(self.leaf_iter())

    def find_common(self, x,dx, y,dy):
        res_x = []
        res_y = []
        while dx > dy:
            res_x.append(x)
            x = x.parent
            dx -= 1
        while dy > dx:
            res_y.append(y)
            y = y.parent
            dy -= 1
        while x != y:
            res_x.append(x)
            res_y.append(y)
            x = x.parent
            y = y.parent
        return res_x, res_y, x

    def get_proven(self):
        return self.root.closed_with
    def print_goals(self):
        print("Goals:")
        for node,d in self.leaf_iter():
            print("*", node.term)
