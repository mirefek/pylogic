from term import Term, TermApp, BVar, TermConstant, TermVariable

class Unification:
    # frozen = None -- nothing frozen
    # frozen = [(), None, None, ()] -- 1,2 frozen
    # frozen = [(x), None, None, (x,y)] -- 1,2 frozen, x frozen, y frozen in 0
    def __init__(self, frozen = None):
        self.to_glue = []
        self._encountered = set()
        self._var_side_copy = dict() # (var, ori_side, new_side) -> var
        self._var_copy_to_ori = dict() # var, new_side -> var, ori_side
        self._var_assignments = dict() # (var, side) -> (term, side)
        self._term_assignments = dict() # (term, side) -> (term, side)
        self.frozen = frozen
        self._var_deps = dict()
        self._basic_req_log = []

    def add_requirement(self,t1,side1,t2,side2, label = "Unify:"):
        self.to_glue.append(((t1,side1),(t2,side2)))
        self._basic_req_log.append((t1,t2,label))
    def print_requirements(self):
        print("frozen:", self.frozen)
        for t1,t2,label in self._basic_req_log:
            print(label)
            print('*', t1)
            print('*', t2)

    def run(self):
        stack = self.to_glue
        self.to_glue = []
        stack.reverse()
        postponed = []
        postponed_should_update = False
        force_assign = False
        while stack or (postponed and (postponed_should_update or not force_assign)):
            if not stack:
                stack = postponed
                self._encountered.difference_update(postponed)
                postponed = []
                if not postponed_should_update: force_assign = True
            x1,x2 = stack.pop()
            #print("unify", str(x1[0]),x1[1], str(x2[0]),x2[1])
            if (x1,x2) in self._encountered: continue
            x1 = self._get_assigned(x1)
            x2 = self._get_assigned(x2)
            #print("assigned", str(x1[0]),x1[1], str(x2[0]),x2[1])
            if x1 == x2: continue
            if self._should_swap(x1,x2): x1,x2 = x2,x1
            if (x1,x2) in self._encountered: continue
            self._encountered.add((x1,x2))

            t1,side1 = x1
            t2,side2 = x2

            if self._is_assignable(t1.f, side1):
                if t1.f == t2.f and side1 == side2 and t1.equals_to(t2):
                    continue
                assign_result = self._assign(t1,side1, t2,side2)
                if force_assign:
                    if self._rename(t1,side1, t2,side2):
                        stack.extend(
                            ((st1, side1), (st2, side2))
                            for st1, st2 in zip(reversed(t1.args), reversed(t2.args))
                        )
                    force_assign = False
                    assign_result = True
                if assign_result is None: # postpone
                    if not postponed:
                        postponed_should_update = False
                    postponed.append((x1,x2))
                elif not assign_result: # failed
                    return False
                else:
                    postponed_should_update = True

            else:
                if t1.f != t2.f: return False
                stack.extend(
                    ((st1, side1), (st2, side2))
                    for st1, st2 in zip(reversed(t1.args), reversed(t2.args))
                )

        return True

    def export_substitutions(self, variables_per_side, new_var_generator = None):

        # find
        # * unset variables
        # * dependencies
        # * side copies

        unset_variables_per_side = [
            set(x)
            for x in variables_per_side
        ]
        fw_deps = dict()
        bw_deps = dict()
        for src_key, (dest_term,dest_side) in self._var_assignments.items():
            if src_key in self._var_copy_to_ori: continue
            src_var,src_side = src_key
            assert src_var in variables_per_side[src_side]
            unset_variables_per_side[src_side].discard(src_var)
            cur_fw_deps = set()
            for dest_var in dest_term.free_vars:
                dest_var_real, dest_side_real = self._var_side_copy.get(
                    dest_var, (dest_var, dest_side)
                )
                
                assert dest_var_real in variables_per_side[dest_side_real]
                dest_key = dest_var_real, dest_side_real
                cur_bw_deps = bw_deps.setdefault(dest_key, [])
                cur_bw_deps.append(src_key)
                if dest_key in self._var_assignments:
                    cur_fw_deps.add(dest_key)
            fw_deps[src_key] = cur_fw_deps

        # find side copies per variable key

        side_copies = dict()
        for (ori_v, ori_side, new_side), new_v in self._var_side_copy.items():
            copies = side_copies.setdefault((ori_v, ori_side), [])
            copies.append((new_v, new_side))

        # resolve variable clashes

        variable_clashes = []
        if self.frozen is None:
            frozen = [set() for _ in variables_per_side]
        else:
            frozen = [
                (fr if fr is not None else vs)
                for i,(vs,fr) in enumerate(zip(variables_per_side, self.frozen))
            ]
        unset_variables_total = set().union(*frozen)
        for cur_vars, cur_frozen in zip(reversed(unset_variables_per_side), reversed(frozen)):
            cur_clashes = list((cur_vars & unset_variables_total) - cur_frozen)
            cur_clashes.sort(key = lambda v: v.name)
            variable_clashes.append(cur_clashes)
            unset_variables_total |= cur_vars
        used_names = set(v.name for v in unset_variables_total)
        side_substs = []
        for cur_clashes in variable_clashes:
            cur_subst = dict()
            side_substs.append(cur_subst)
            for v in cur_clashes:
                if new_var_generator is not None:
                    new_v = new_var_generator(v, used_names)
                    used_names.add(new_v.name)
                    cur_subst[v] = new_v.to_term()
        del variable_clashes
        side_substs.reverse()

        # set substitution for copies of unset variables

        for (ori_v,ori_side), copy_keys in side_copies.items():
            if ori_v not in unset_variables_per_side: continue
            term = self.side_subst[ori_side].get(ori_v, ori_v)
            for copy_v, copy_side in copy_keys:
                # either original ori_v, or its renaming to deal with clashes
                self.side_subst[copy_side][copy_v] = term

        # gradually set substitution of set variables with no more forward deps

        final = [key for key,fw in fw_deps.items() if not fw]
        while final:
            key = final.pop()
            
            v,side = key
            for bw_key in bw_deps.get(key, ()): # remove from dependencies
                fw_keys = fw_deps[bw_key]
                fw_keys.remove(key)
                if not fw_keys: final.append(bw_key) # find new final variables

            # main part
            term, term_side = self._var_assignments[key] # find the appropriate term
            term = term.substitute_free(side_substs[term_side]) # set the substitution
            side_substs[side][v] = term

            # if v has copies, set them the same
            for copy_v, copy_side in side_copies.get(key, ()):
                side_substs[copy_side][copy_v] = term

            # remove processsed from fw_deps (for check)
            del fw_deps[key]
        assert not fw_deps

        # remove auxiliary copies from the result
        for v,side in self._var_copy_to_ori.keys():
            cur_side_subst = side_substs[side]
            if v in cur_side_subst:
                del cur_side_subst[v]
        
        return side_substs

    def _is_assignable(self, v, side):
        if v is None: return False # bound variable
        if isinstance(v, TermConstant): return False
        v,side = self._var_copy_to_ori.get((v,side), (v,side))
        if self.frozen is not None and (
                self.frozen[side] is None or
                v in self.frozen[side]
        ): return False
        return True

    def _assign(self, t1,side1, t2,side2):
        v1 = t1.f
        v1,side1v = self._var_copy_to_ori.get((v1,side1), (v1,side1))
        #print("Assign:", v1, side1v, t2, side2)
        if t1.f.arity == 0:
            if t2.debruijn_height > 0: return False
            t2_abstract = t2
        elif any(isinstance(x, TermApp) for x in t1.args): return None
        elif t2.debruijn_height == 0:
            t2_abstract = t2
        else:
            t1_vars = [
                arg.debruijn_height for arg in t1.args
            ]
            args = [None]*(max(t1_vars)+1)
            duplicite_variable = False
            arg_changed = False
            for i,t1v in enumerate(t1_vars):
                if args[t1v] is not None:
                    duplicite_variable = True
                    break
                else:
                    args[t1v] = BVar(v1.arity-i)
                    if t1v != args[t1v].debruijn_height-1:
                        arg_changed = True
            for tv2 in t2.bound_vars:
                if tv2 >= len(args) or args[tv2] is None:
                    return False # missing variable
            if duplicite_variable: return None

            if not arg_changed: t2_abstract = t2
            else: t2_abstract = t2.substitute_bvars(args, natural_order = False)

        # set & check dependencies
        deps_rec = set()
        for x in set(t2.free_vars):
            x = self._var_copy_to_ori.get((x,side2), (x,side2))
            deps_rec.add(x)
            deps_rec.update(self._var_deps.get(x, ()))
        if (v1,side1v) in deps_rec:
            return False
        self._var_deps[v1,side1v] = deps_rec

        self._var_assignments[v1,side1v] = t2_abstract,side2
        self._term_assignments[t1,side1] = t2,side2
        return True

    def _rename(self, t1,side1, t2,side2):
        if t1.f.arity != t2.f.arity: return False
        v1 = t1.f
        v1,side1v = self._var_copy_to_ori.get((v1,side1), (v1,side1))

        # set & check dependencies
        deps_rec = set()
        for x in set(t2.free_vars):
            x = self._var_copy_to_ori.get((x,side2), (x,side2))
            deps_rec.add(x)
            deps_rec.update(self._var_deps.get(x, ()))
        if (v1,side1v) in deps_rec:
            return False
        self._var_deps[v1,side1v] = deps_rec

        self._var_assignments[v1,side1v] = t2.f.to_term(),side2
        self._term_assignments[t1,side1] = t2,side2
        return True

    
    def _get_assigned(self, x):
        x2 = self._get_assigned_step(x)
        if x2 is None: return x
        x3 = self._get_assigned_step(x2)
        if x3 is None: return x2
        # shorten the path if necessary
        path = [x,x2,x3]
        x3 = self._get_assigned_step(x3)
        while x3 is not None:
            path.append(x3)
            x3 = self._get_assigned_step(x3)
        x3 = path.pop()
        for x2 in path:
            if x2[0].arity == 0:
                self._var_assignments[x2[0].f, x2[1]] = x3
            self._term_assignments[x2] = x3

    def _get_assigned_step(self, x):
        res = self._term_assignments.get(x, None)
        if res is not None: return res
        term, side = x
        var_key = term.f, side
        var_key = self._var_copy_to_ori.get(var_key, var_key)
        assigned = self._var_assignments.get(var_key, None)
        if assigned is None: return None
        abstract_term, res_side = assigned
        if abstract_term.debruijn_height == 0:
            res_term = abstract_term
        else:
            assert term.f.arity > 0
            args = []
            for i,arg in enumerate(term.args):
                if i+1 not in abstract_term.bound_vars: args.append(None)
                else: args.append(self._move_to_side(arg, side, res_side))
            res_term = abstract_term.substitute_bvars(args)
        self._term_assignments[x] = res_term, res_side
        return res_term, res_side

    def _move_to_side(self, t, ori_side, new_side):
        if ori_side == new_side: return t
        ori_vars = t.free_vars
        if not ori_vars: return t
        ori_vars = list(ori_vars)
        new_vars = []
        for ori_v in ori_vars:
            ori_key = ori_v, ori_side
            real_ori_v, real_ori_side = self._var_copy_to_ori.get(ori_key, ori_key)
            new_v = self._var_side_copy.get((real_ori_v, real_ori_side, new_side), None)
            if new_v is None:
                new_v = TermVariable(real_ori_v.arity, real_ori_v.name)
                self._var_side_copy[real_ori_v, real_ori_side, new_side] = new_v
                self._var_copy_to_ori[new_v, new_side] = real_ori_v, real_ori_side
            new_vars.append(new_v)
        return t.substitute_free({
            ori_v : new_v.to_term()
            for ori_v, new_w in zip(ori_vars, new_vars)
        })

    def _should_swap(self, x1,x2):
        t1,side1 = x1
        t2,side2 = x2
        as1 = bool(self._is_assignable(t1.f, side1))
        as2 = bool(self._is_assignable(t2.f, side2))
        if not (as1 or as2): return False
        if not (as1 and as2): return as2
        if t1.debruijn_height != t2.debruijn_height:
            return t1.debruijn_height < t2.debruijn_height
        if t1.debruijn_height > 0:
            if len(t1.bound_vars) != len(t2.bound_vars):
                return len(t1.bound_vars) < len(t2.bound_vars)
        if t1.f.arity != t2.f.arity:
            return t1.f.arity > t2.f.arity
        return side1 > side2

# TESTS

if __name__ == "__main__":
    from term import get_unused_name
    from logic_core import LogicCore
    from parse_term import TermParser
    import traceback
    from calculator import Calculator

    logic = LogicCore()
    calculator = Calculator(logic)
    calculator.accept_types(int)
    parser = TermParser(logic, int_to_term = lambda n: calculator.get_value_term(n))
    parser.parse_file("axioms_logic")
    parser.parse_file("axioms_set")
    parser.parse_file("axioms_fun")
    parser.parse_file("axioms_numbers")
    parser.parse_file("axioms_thibault")

    def get_new_var(v, used_names):
        name = get_unused_name(v.name, used_names)
        return parser.get_var(name, v.arity)
    
    def test_unification(t1, t2, frozen = ((),()), single_side = False):
        print()
        t1 = parser.parse_str(t1)
        t2 = parser.parse_str(t2)
        if frozen == ((),()) and single_side: frozen = ((),)
        frozen = list(frozen)
        for i,fr in enumerate(frozen):
            if fr is not None:
                frozen[i] = set(
                    parser.get_var(v, 0)
                    for v in fr
                )
        unif = Unification(frozen)
        unif.add_requirement(t1,0,t2,int(not single_side))
        if unif.run():
            print("Unification successful")
            if single_side: free_vars = [t1.free_vars | t2.free_vars]
            else: free_vars = [t1.free_vars, t2.free_vars]
            substs = unif.export_substitutions(free_vars, get_new_var)
            for side, subst in enumerate(substs):
                print("Side", side)
                for key, val in subst.items():
                    print('  ', key, ':=', val)
        else:
            print("Unification failed")

    print()
    print("Nested unification")
    test_unification('((A = A) => (V = (true && false))) = (X => X)', 'X = X')
    print()
    print("Variable renaming")
    test_unification('X = (A && B)', '(A && B) = X')
    print()
    print("Frozen variables")
    test_unification('X = (A && B)', '(A && B) = X', frozen = (('A','B'),('B',)))
    print()
    print("Cycles")
    test_unification("A || B", "(B && true) || (A && true)")
    test_unification("A = (A && true)", "X = X")
    print()
    print("Binders")
    test_unification('forall(x : BODY(x)) = forall(y : y && C)', "X = X")
    test_unification('forall(x : BODY(x)) && C && (G => false)',
                     'forall(y : y && C) && (X || true) && C')
    test_unification('forall(x : BODY(x)) || BODY(A) || A', 'forall(x : x) || true || B')
    test_unification('forall(x : BODY(x)) || BODY(C)', 'forall(y : y && C) || (true && X)')
    test_unification('BODY(X) || forall(x : BODY(x))', '(true && false) || forall(y : y)')
    test_unification('forall(x : BODY(x)) || forall(x : forall(y : BODY(x) || BODY(y)))',
                     'forall(x : x && X) || A')
    test_unification('forall(x : BODY(x)) || forall(x : forall(y : BODY(x) || BODY(y)))',
                     'forall(x : exists(y : x && y)) || A')

    print()
    print("Same side")
    test_unification("X", "X", single_side = True)
    print()
    print("Binders postpone")
    test_unification(
        "PRED(X) => exists(x : PRED(x))",
        "!to_bool1(PRED2(Y)) => exists(x : !to_bool1(PRED2(x)))",
        frozen = ((), None),
    )
    test_unification(
        "PRED(X) => PRED2(X)",
        "PRED(X) => PRED2(X)",
        frozen = ((), ()),
    )
    test_unification(
        "forall(x : forall(y : PRED(x, y))) => forall(y : PRED(X, y))",
        "forall(x : forall(y : PRED(x, y))) => forall(y : PRED(X, y))",
        frozen = ((), None),
    )
    test_unification(
        "domain(f) is_Set",
        "domain(require f is_Fun ; fun(y : unique(x : f [ x ] = y))) is_Set",
        frozen = ((), None),
    )
    test_unification(
        "loop(A, B, x : y : x + BODY(y))",
        "loop(A % 2, 5, a : b : a + a)",
        frozen = ((), None),
    )
