from logic_env import LogicEnv
from tactics import apply_spec, Intros, PatternLookupGoal, ApplyExact, BasicTactic
from term import Term, TermFunction, get_unused_name
from logic_core import AssumptionLabel
from pytheorem import Theorem, Resolver
from pattern_lookup import PatternLookupRewrite

env = LogicEnv()
g = env.goal_env
co = env.constants
axiom = env.axioms

with g.goal("X => !!X"):
    g.rw(co._neg, repeat = True)
    x, x_to_f = g.intros()
    f = x_to_f(x)
    g.exact(f)

dneg_rev = g.last_proven

with g.goal("(A => B) => (B => C) => (A => C)"):
    ab, bc, a = g.intros()
    g.exact(bc(ab(a)))

chain = g.last_proven

with g.goal("!X => X => false"):
    nx, x = g.intros()
    g.exact(nx.rw(co._neg)(x))

contr = g.last_proven
print(contr)

env.tactics.register("by_contradiction", axiom.double_neg.rw(co._neg, position=[0]))
env.tactics.register("by_contradiction", env.defs._neg.symm.to_impl())

with g.goal("(!X => X) => X"):
    a = g.intros()
    nx = g.app(axiom.double_neg).rw(co._neg).intros()
    g.exact(contr(nx, a(nx)))

assump_neg = g.last_proven
print("assump_neg:", assump_neg)

with g.goal("(A => X) => (!A => X) => X"):
    ax, nax = g.intros()
    g.by_contradiction()
    nx = g.intro().rw(co._neg)
    na = chain(ax,nx)
    na = na.rw(env.defs._neg.symm)
    g.exact(nx(nax(na)))

cases_bool = g.last_proven

with g.goal("A || B => (A => X) => (B => X) => X"):
    ab, ax, bx = g.intros()
    ab = ab.rw(co._or)
    g.app(cases_bool(ax))
    na = g.intro()
    g.app(bx).app(ab).exact(na)
    print("ab", ab)

cases_or = g.last_proven
env.add_impl_rule("to_cases", cases_or)

with g.goal("A => A || B"):
    g.rw(co._or)
    a, na = g.intros()
    g.app(axiom.false(contr(na, a)))


or_intro1 = g.last_proven
print(or_intro1)
env.tactics.register("choose0", or_intro1)

with g.goal("B => A || B"):
    g.rw(co._or)
    b, na = g.intros()
    g.exact(b)
or_intro2 = g.last_proven
print(or_intro2)
env.tactics.register("choose1", or_intro2)

def choose(env, node, *nums):
    c0 = env.tactics.get_tactic("choose0")
    c1 = env.tactics.get_tactic("choose1")
    for i,n in enumerate(nums):
        if i > 0:
            c0(env, node)
            [node] = node.children
        for _ in range(n):
            c1(env, node)
            [node] = node.children

env.tactics.register("choose", choose)

with g.goal("A && B => A"):
    g.rw(co._and).rw(co._neg)
    assump = g.intro()
    na = g.by_contradiction().intro()
    g.app(assump)
    g.choose0().assumed()

split_and1 = g.last_proven
print("split_and1:", split_and1)

with g.goal("A && B => B"):
    g.rw(co._and).rw(co._neg)
    assump = g.intro()
    nb = g.by_contradiction().intro()
    g.app(assump)
    g.choose1().exact(nb)

split_and2 = g.last_proven
print("split_and2:", split_and2)

with g.goal("A => B => A && B"):
    g.rw(co._and).rw(co._neg)
    a,b,ab = g.intros()
    g.app(cases_or(ab))
    g.exact(contr(0,a))
    g.exact(contr(0,b))

and_intro = g.last_proven
print("and_intro:", and_intro)
env.tactics.register("cases_goal", and_intro)

env.add_impl_rule("split", split_and1, split_and2)

h = env.hypothesis('tmp', "X || Y")
h1 = h.apply_rule("to_cases")
print(h1)

def cases_tactic(env, node, *args):
    if not args:
        tactic = env.tactics.get_tactic("cases_goal")
        return tactic(env, node)
    else:
        nodes = [node]
        for t in args:
            assert isinstance(t, (str,Term,Theorem))
            if isinstance(t, Theorem):
                thm = t.apply_rule("to_cases")
                app = lambda node: apply_spec(env, node, thm)
            else:
                t = env.to_term(t)
                thm = cases_bool(A = t, X = node.term)
                app = lambda node: ApplyExact(env, node, thm, 2)
            next_nodes = []
            for node in nodes:
                app(node)
                for c in node.children:
                    Intros(env, c, 1)
                    next_nodes.append(c.children[0])
            nodes = next_nodes

env.tactics.register("cases", cases_tactic)

x = env.basic_impl.refl(env.to_term("false"))
thm_not_false = x.rw(env.defs._neg.symm)
thm_true = thm_not_false.rw(env.defs.true.symm)

with g.goal("X is_bool => Y is_bool => (X => Y) => (Y => X) => X = Y"):
    x_bool, y_bool, xy, yx = g.intros()
    x_bool = x_bool.rw(co._is_bool)
    y_bool = y_bool.rw(co._is_bool)
    xf,yf = g.cases(x_bool, y_bool)
    yt = g.rw(xf).rw(yf).app(axiom.eq_refl)
    with g.goal("A = true => B = false => (A => B) => C"):
        a,b,c = g.intros()
        c = c.rw(a).rw(b)
        g.app(axiom.false(c(thm_true)))
    xt,yf = g.app(g.last_proven(yt,xf,yx))
    yt = g.app(g.last_proven(xt,yf,xy))
    g.rw(xt).rw(yt).app(axiom.eq_refl)

class TypingResolver(Resolver):
    def __init__(self, env, last_check = None):
        self.env = env
        self.last_check = last_check
    def run(self, label, core_thm):
        cur_check = core_thm.assumption(label)
        if self.last_check is not None:
            if cur_check is self.last_check: return self
            if cur_check.equals_to(self.last_check):
                return TypingResolver(self.env, cur_check)
        typing_tactic = self.env.tactics.get_tactic("typing")
        thm_n = typing_tactic.find_first(cur_check)
        if thm_n is None:
            return TypingResolver(self.env, cur_check)
        thm, n = thm_n
        if n > 0 or thm.has_assumptions:
            return TypingResolver(self.env, cur_check)
        return self.resolve_with(label, core_thm, thm.core_thm)

env.tactics.register("typing", axiom.eq_is_bool)
env.tactics.register("typing", axiom.impl_is_bool)
env.tactics.register("typing", axiom.is_sane_is_bool)

bool_eq_by_equiv = g.last_proven
bool_eq_by_equiv = bool_eq_by_equiv.set_resolver(TypingResolver(env), "typing1")
bool_eq_by_equiv = bool_eq_by_equiv.set_resolver(TypingResolver(env), "typing2")

with g.goal("false is_bool"):
    g.rw(co._is_bool)
    g.choose0().app(axiom.eq_refl)
env.tactics.register("typing", g.last_proven)

def prove_basic_typing(term):
    with g.goal(term):
        c = g.current_goal.term.args[0].f
        g.rw(c, position = [0])
        g.typing()
    env.tactics.register("typing", g.last_proven)

prove_basic_typing("!X is_bool")
prove_basic_typing("true is_bool")
prove_basic_typing("(X || Y) is_bool")
prove_basic_typing("(X && Y) is_bool")
prove_basic_typing("(X ^^ Y) is_bool")
prove_basic_typing("(X <=> Y) is_bool")
prove_basic_typing("(X is_bool) is_bool")
prove_basic_typing("to_bool(X) is_bool")
prove_basic_typing("to_bool1(X) is_bool")
prove_basic_typing("exists(x : PRED(x)) is_bool")
prove_basic_typing("forall(x : PRED(x)) is_bool")

to_bool_elim = axiom.double_neg.rw(env.defs.to_bool.symm)
to_bool_intro = dneg_rev.rw(env.defs.to_bool.symm)

with g.goal("(A <=> B) => (A => B)"):
    ab, a = g.intros()
    ab = ab.rw(co._equiv)
    g.app(to_bool_elim)
    a = to_bool_intro(a)
    g.app(ab(a))
env.add_impl_rule("to_impl", g.last_proven)

with g.goal("to_bool(X) = X"):
    g.app(bool_eq_by_equiv)
    g.exact(to_bool_elim)  # to_bool(X) => X
    g.exact(to_bool_intro)    # X => to_bool(X)

is_bool_to_bool_eq = g.last_proven(typing2 = "typing")
print(is_bool_to_bool_eq)

with g.goal("(A <=> B) = (A = B)"):
    g.rw(co._equiv)
    g.rw(is_bool_to_bool_eq(typing = "typing1"), position = [0,0])
    g.rw(is_bool_to_bool_eq(typing = "typing2"), position = [0,1])
    g.app(axiom.eq_refl)

equiv_is_eq = g.last_proven

with g.goal("X => X = true"):
    x = g.intro()
    g.app(bool_eq_by_equiv)
    g.intro()    # X => true
    g.app(thm_true)
    g.intro()    # true => X
    g.exact(x)

to_eq_true = g.last_proven

with g.goal("!X => X = false"):
    nx = g.intro()
    g.app(bool_eq_by_equiv)
    x = g.intro()         # to_bool(X) => false
    g.exact( contr(nx, x) )
    g.app(axiom.false,0)   # false => to_bool(X)

to_eq_false = g.last_proven

def to_eq(thm):
    term = thm.term
    if term.f == co._neg:
        rule = to_eq_false
        term = term.args[0]
    else:
        rule = to_eq_true
    return rule(thm)

autoconvert = dict()
autoconvert["reduce"] = PatternLookupRewrite()
def add_autoconvert(thm, c, i):
    autoconvert[c,i] = thm
    autoconvert["reduce"] = autoconvert["reduce"].add_rule(thm.symm)

with g.goal("(A => B) = (A => to_bool(B))"):
    g.app(bool_eq_by_equiv)
    ab,a = g.intros()
    g.exact(to_bool_intro(ab(a)))
    abb,a = g.intros()
    g.exact(to_bool_elim(abb(a)))

add_autoconvert(g.last_proven, co._impl, 1)

with g.goal("(A => B) = (to_bool(A) => B)"):
    g.app(bool_eq_by_equiv)
    ab,aa = g.intros()
    g.exact(ab(to_bool_elim(aa)))
    aab,a = g.intros()
    g.exact(aab(to_bool_intro(a)))

add_autoconvert(g.last_proven, co._impl, 0)

def prove_autoconvert_by_definition(constant, *ii):
    for i in ii:
        c_def = env.defs[constant]
        header, _ = env.split_eq(c_def.term)
        args = list(header.args)
        args[i] = Term(co.to_bool, (args[i],))
        header2 = Term(constant, args)
        goal = Term(co._eq, (header, header2))
        with g.goal(goal):
            g.rw(constant, position = [0])
            g.rw(constant, position = [1])
            g.rw(autoconvert["reduce"])
            g.app(axiom.eq_refl)
        add_autoconvert(g.last_proven, constant, i)

prove_autoconvert_by_definition(co._neg, 0)
prove_autoconvert_by_definition(co._or, 0,1)
prove_autoconvert_by_definition(co._and, 0,1)
prove_autoconvert_by_definition(co.to_bool, 0)
prove_autoconvert_by_definition(co._equiv, 0,1)
prove_autoconvert_by_definition(co._xor, 0,1)

with g.goal("(if C ; X else Y) = (if to_bool(C) ; X else Y)"):
    c = g.cases("C")
    with g.subgoal():
        g.rw(axiom.if_true(c))
        g.rw(axiom.if_true(to_bool_intro(c)))
        g.app(axiom.eq_refl)
    nc = g.get_last_output()
    g.rw(axiom.if_false(nc))
    with g.goal("!to_bool(C)"):
        g.rw(co.to_bool)
        g.exact(dneg_rev(nc))
    g.rw(axiom.if_false(g.last_proven))
    g.app(axiom.eq_refl)

add_autoconvert(g.last_proven, co._if, 0)

with g.goal("PRED(X) => PRED(Y) => PRED(if C; X else Y)"):
    px,py = g.intros()
    c = g.cases("C")
    g.rw(axiom.if_true(c)).exact(px)
    nc = g.get_last_output()
    g.rw(axiom.if_false(nc)).exact(py)

if_common = g.last_proven

with g.goal("PRED(X) => exists(x : PRED(x))"):
    g.rw(co.exists).rw(autoconvert["reduce"])
    g.exact(axiom.example_universal)

exists_intro = g.last_proven
exists_elim = env.defs.exists.to_impl().rw(autoconvert["reduce"])

print(exists_intro) # PRED(X) => exists(x : PRED(x))
print(exists_elim)  # exists(x : PRED(x)) => PRED(example(x : PRED(x)))
eq_symm = env.rewriter._eq_symm

with g.goal("(X = Y) = (Y = X)"):
    g.app(bool_eq_by_equiv)
    g.app(eq_symm,0).app(eq_symm,0)

eq_symm_rw = g.last_proven
print(eq_symm_rw)

with g.goal("PRED(X) => !PRED(Y) => X != Y"):
    px, py = g.intros()
    xy = g.rw(co._neg).intros()
    g.exact(contr(py, px.rw(xy)))

neq_by_pred = g.last_proven
print(neq_by_pred)

bool_calc = PatternLookupRewrite()
def add_bool_calc(rule):
    global bool_calc
    bool_calc = bool_calc.add_rule(rule)

with g.goal("(X => true) = true"):
    g.app(bool_eq_by_equiv)
    g.intro()
    g.exact(thm_true)
    g.intros()
    g.exact(thm_true)

add_bool_calc(g.last_proven)
add_bool_calc(env.defs._neg.symm) # (X => false) = !X

with g.goal("(true => X) = X"):
    g.app(bool_eq_by_equiv)
    tx = g.intro()
    g.exact(tx(thm_true))
    x,_ = g.intros()
    g.exact(x)

add_bool_calc(g.last_proven)

with g.goal("(false => X) = true"):
    g.app(bool_eq_by_equiv)
    g.intros()
    g.exact(thm_true)
    g.intro()
    g.app(axiom.false,0)

add_bool_calc(g.last_proven)
add_bool_calc(env.defs.true.symm)

with g.goal("!!X = X"):
    g.app(bool_eq_by_equiv)
    g.exact(axiom.double_neg).exact(dneg_rev)

double_neg_eq = g.last_proven

def prove_bool_calc(term):
    term = env.to_term(term)
    c = term.args[0].f
    with g.goal(term):
        g.rw(c)
        g.rw(bool_calc, repeat = True)
        x,y = env.split_eq(g.current_goal.term)
        if not x.equals_to(y):
            g.rw(double_neg_eq, repeat = True)
        g.app(axiom.eq_refl)
    add_bool_calc(g.last_proven)

prove_bool_calc("!true = false")
prove_bool_calc("(true || X) = true")
prove_bool_calc("(X || true) = true")
prove_bool_calc("(false || X) = X")
prove_bool_calc("(X || false) = X")

with g.goal("to_bool1(X) = X"):
    g.rw(co.to_bool1)
    x_sane = axiom.bool_is_sane.set_resolver(TypingResolver(env), "typing2")
    xnn = neq_by_pred(PRED = "x : x is_sane")(x_sane, axiom.null_is_not_sane)
    g.rw(to_eq(xnn)).rw(bool_calc).app(axiom.eq_refl)
    root = g.current_ctx.tree.root

print(g.last_proven)
to_bool1_idemp = g.last_proven

with g.goal("(!A => B) => (!B => A)"):
    nab,nb = g.intros()
    na = g.by_contradiction().intro()
    g.exact(contr(nb, nab(na)))

nimpl_symm = g.last_proven
x = nimpl_symm(B = "!B")
x = x.rw(env.defs.to_bool.symm)
x = x.rw(autoconvert["reduce"])
contraposition = x
x = x(A = "!A")
x = x.rw(env.defs.to_bool.symm)
x = x.rw(autoconvert["reduce"])
impln_symm = x
x = x(B = "!B")
x = x.rw(env.defs.to_bool.symm)
x = x.rw(autoconvert["reduce"])
contraposition_rev = x

null_to_false = chain(to_bool_intro, axiom.null_to_bool.to_impl())
null_to_any = chain(null_to_false, axiom.false)
req_true = axiom.if_true(B = "null").rw(env.defs._require.symm)
req_false = axiom.if_false(B = "null").rw(env.defs._require.symm)

with g.goal("(require A; B) => A"):
    req = g.intro()
    na = g.by_contradiction().intro()
    g.exact(null_to_false(req.rw(req_false(na))))
split_req1 = g.last_proven

with g.goal("(require A; B) => B"):
    req = g.intro()
    a = g.cases("A")
    g.exact(req.rw(req_true(a)))
    na = g.get_last_output()
    g.app(null_to_any)
    g.exact(req.rw(req_false(na)))
split_req2 = g.last_proven

print(split_req1)
print(split_req2)
env.add_impl_rule("split", split_req1, split_req2)

x = exists_intro(PRED = "x : !to_bool1(PRED(x))")
x = nimpl_symm(x)
x = x.rw(env.defs.forall.symm)
forall_elim_full = x

x = exists_elim(PRED = "x : !to_bool1(PRED(x))")
x = impln_symm(x)
x = x.rw(env.defs.forall.symm)
forall_intro_full = x

with g.goal("X => to_bool1(X)"):
    g.rw(co.to_bool1)
    g.app(or_intro2, 0)

to_bool1_intro = g.last_proven
forall_intro = chain(to_bool1_intro, forall_intro_full)
print(forall_intro)

forall_elim = forall_elim_full.rw(to_bool1_idemp)
forall_eq_elim = forall_elim(PRED = "x : BODY1(x) = BODY2(x)")
forall_forall_elim = forall_elim(PRED = "x : forall(y : PRED(x,y))")

def generalize(thm, v):
    if isinstance(v, str):
        v = env.parser.get_var(v, 0)
    pred = thm.term.substitute_free({ v : Term(1) })
    x = Term(co.to_bool1, (pred,))
    x = Term(co._neg, (x,))
    x = Term(co.example, (x,), (['x'],))
    example = x
    thm = thm.specialize({ v : example })
    x = forall_intro(PRED = pred)
    x = x.modus_ponens_basic(thm)
    return x

env.generalize = generalize

with g.goal("forall(x : PRED(x) = PRED2(x)) => example(x : PRED(x)) = example(x : PRED2(x))"):
    assump = g.intro()
    ex = g.cases("PRED(example(x : PRED2(x)))")
    assump_eq = forall_eq_elim(assump)
    with g.subgoal():
        g.app(axiom.example_well_founded)
        with g.goal("PRED(X) => PRED2(X)"):
            print(g.current_goal)
            g.exact(assump_eq.to_impl())
        g.exact(generalize(g.last_proven, 'X'))
        g.exact(ex)
    nex = g.get_last_output()
    with g.subgoal():
        nex2 = nex.rw(assump_eq)
        nex1 = contraposition_rev(
            axiom.example_universal(
                PRED = "x : PRED2(x)",
                X = "example(x : PRED(x))"
            ),
            nex2,
        ).rw(assump_eq.symm)

        g.rw(axiom.example_null(nex1))
        g.exact(axiom.example_null(nex2).symm)

example_ext = g.last_proven
env.rewriter.add_extensionality(example_ext)

#x = or_intro1.generalize('A', 'B')
x = axiom.eq_refl(X = "example(X : ((X && Y) || Y) && Z)")
print(x)
x = x.rw(co._or)
print(x)

def prove_extensionality_by_definition(constant, index = None):
    if index is None:
        for index, numb in enumerate(constant.signature):
            if numb > 0: prove_extensionality_by_definition(constant, index)
        return

    numb = constant.signature[index]
    assert numb > 0
    PRED = env.parser.get_var("PRED", 1)
    X = env.parser.get_var("X", 0)
    BODY1 = env.parser.get_var("BODY1", numb)
    BODY2 = env.parser.get_var("BODY2", numb)
    used_names = set()
    bound_names_common = []
    for _ in range(max(constant.signature)):
        name = get_unused_name('x', used_names)
        bound_names_common.append(name)
        used_names.add(name)
    bound_names_common = tuple(bound_names_common)
    bound_names = tuple(
        bound_names_common[:numb2]
        for numb2 in constant.signature
    )
    bound_names_main = bound_names[index]
    used_names = set()
    vs = []
    for i2,numb2 in enumerate(constant.signature):
        if i2 == index: vs.append(BODY1)
        else:
            v = env.get_locally_fresh_var(
                TermFunction((0,)*numb2, True, "A"),
                used_names,
            )
            used_names = v.name
            vs.append(v)
    args1 = [v.to_term() for v in vs]
    args2 = list(args1)
    args2[index] = BODY2.to_term()
    assump = Term(env.core.equality, (args1[index], args2[index]))
    for bname in reversed(bound_names_main):
        assump = Term(co.forall, (assump,), bound_names = ((bname,),))
    lhs = Term(constant, args1, bound_names = bound_names)
    rhs = Term(constant, args2, bound_names = bound_names)
    main_eq = Term(env.core.equality, (lhs, rhs))
    ext_goal = Term(env.core.implication, (assump, main_eq))
    with g.goal(ext_goal):
        a = g.intro()
        g.rw(constant, position=[0]).rw(constant, position=[1])
        for _ in range(numb-1): a = forall_forall_elim(a)
        a = forall_eq_elim(a)
        g.rw(a, position = [0], repeat = True)
        g.app(axiom.eq_refl)
    env.rewriter.add_extensionality(g.last_proven)
    print(g.last_proven)

prove_extensionality_by_definition(co.exists)
prove_extensionality_by_definition(co.forall)
prove_extensionality_by_definition(co.exists_uq)
co_unique = co["unique", 1]
prove_extensionality_by_definition(co_unique)
prove_extensionality_by_definition(co.take)
prove_extensionality_by_definition(co.let)

class SubstResolver(Resolver):
    def __init__(self, env, last_check_fail = None):
        self.env = env
        self.last_check_fail = last_check_fail
    def run(self, label, core_thm):
        aterm = core_thm.assumption(label)
        v = aterm.args[0].f
        if self.last_check_fail is not None and self.last_check_fail is not label:
            if self.last_check_fail is True: return self
            aterm2 = core_thm.assumption(self.last_check_fail)
            if aterm2 is not None and v in aterm2.free_vars:
                return self
        if v in core_thm.term.free_vars: return self
        for label2, aterm2 in core_thm.assump_items():
            if label2 == label:
                if v in aterm2.args[1].free_vars:
                    return SubstResolver(self.env, True)
            elif v in aterm2.free_vars:
                return SubstResolver(self.env, label2)

        assert v.is_free_variable and v.arity == 0
        assert aterm.f == self.env.core.equality
        value = aterm.args[1]
        core_thm = core_thm.specialize({ v : value })
        return self.resolve_with(label, core_thm, self.env.axioms.eq_refl(X = value))    

with g.goal("exists(x : PRED(x)) => A = example(x : PRED(x)) => PRED(A)"):
    assump, eq = g.intros()
    g.rw(eq)
    g.exact(exists_elim(assump))

exists_elim_eq = g.last_proven
print(exists_elim_eq)
def get_example(thm, v = None, label = "_SUBST_"):
    assert thm.term.f == env.constants.exists
    if v is None:
        [[v]] = thm.term.bound_names
        v = v.upper()
    if isinstance(v, str):
        v = env.parser.get_var(v,0)
    if v in thm.term.free_vars:
        v = env.get_locally_fresh_var(v, set(x.name for x in thm.term.free_vars))
    if isinstance(label, str):
        label = AssumptionLabel(label)
    thm = exists_elim_eq(thm, A = v.to_term())
    assert label not in thm.assump_labels()
    thm = thm.set_resolver(SubstResolver(env), label)
    thm = thm.freeze(thm.assumption(label).free_vars)
    return v, thm

def local_def(term, label = "_EQ_"):
    term = env.to_term(term)
    v, body = env.split_eq(term)
    v = v.f
    assert v.is_free_variable
    assert v.arity == 0
    assert v not in body.free_vars
    if isinstance(label, str): label = AssumptionLabel(label)
    res = env.hypothesis(label, term, frozen = True)
    res = res.set_resolver(SubstResolver(env), label)
    return res

class IntroVar(BasicTactic):
    def get_subgoals(self, v = None):
        assert self.goal.f == self.env.constants.forall
        if v is None:
            [[v]] = self.goal.bound_names
            v = v.upper()
        if isinstance(v, str):
            v = self.env.parser.get_var(v,0)
        if v in self.goal.free_vars:
            v = self.env.get_locally_fresh_var(v, set(x.name for x in self.goal.free_vars))
        self.v = v
        self.outputs = [v]
        subgoal = self.goal.args[0].substitute_bvars([v.to_term()])
        return [subgoal]
    def build_thm(self, thm):
        return thm.generalize(self.v)

env.tactics.register("introv", IntroVar)

with g.goal("exists_uq(x : PRED(x)) => exists(x : PRED(x))"):
    assump = g.intro()
    assump = assump.rw(co.exists_uq)
    v, assump = get_example(assump)
    a1, a2 = assump.split()
    g.exact(exists_intro.modus_ponens_basic(a1))

exists_uq_to_exists = g.last_proven

with g.goal("exists_uq(x : PRED(x)) => PRED(A) => PRED(B) => A = B"):
    ex_uq, pred_a, pred_b = g.intros()
    ex_uq = ex_uq.rw(co.exists_uq)
    x, assump = get_example(ex_uq, 'X')
    pred_x, uq = assump.split()
    uq = forall_elim(uq)
    g.exact(uq(pred_a).rw(uq(pred_b).symm))
exists_uq_is_uq = g.last_proven

with g.goal("exists_uq(x : PRED(x)) => PRED(unique(x : PRED(x)))"):
    ex_uq = g.intro()
    g.rw(co_unique).rw(req_true(ex_uq))
    ex = exists_uq_to_exists(ex_uq)
    g.exact(exists_elim(ex))
exists_uq_unique = g.last_proven

with g.goal("exists_uq(x : PRED(x)) => A = unique(x : PRED(x)) => (PRED(A) && (PRED(B) => B = A))"):
    ex_uq, a_def = g.intros()
    g.cases()
    with g.subgoal("PRED(A)"):
        g.rw(a_def)
        g.exact(exists_uq_unique(ex_uq))
    pred_a = g.last_proven
    pred_b = g.intro()
    g.exact(exists_uq_is_uq(ex_uq, pred_b, pred_a))
exists_uq_elim = g.last_proven

with g.goal("!exists(x : PRED(x)) => unique(x : PRED(x)) = null"):
    nex = g.intro()
    nex_uq = contraposition_rev(exists_uq_to_exists, nex)
    g.rw(co_unique)
    g.app(req_false(nex_uq))
nexists_to_unique_null = g.last_proven

with g.goal("forall(x : PRED(x) => x = A) => PRED(A) => exists_uq(x : PRED(x))"):
    assump, pa = g.intros()
    g.rw(co.exists_uq)
    g.app(exists_intro(X = "A"))
    g.cases().exact(pa)
    g.exact(assump)
exists_uq_intro = g.last_proven

with g.goal("forall(x : PRED(x) => x = A) => PRED(A) => unique(x : PRED(x)) = A"):
    assump, pa = g.intros()
    ex_uq = exists_uq_intro(assump, pa)
    g.app(exists_uq_is_uq)
    g.exact(ex_uq)
    g.exact(exists_uq_unique(ex_uq))
    g.exact(pa)
unique_value = g.last_proven

with g.goal("forall(x : x != null && PRED(x) => x = A) => PRED(A) => unique(x : x != null && PRED(x)) = A"):
    assump, pa = g.intros()
    an = g.cases("A = null")
    with g.goal("!exists(x : x != null && PRED(x))"):
        ex = g.by_contradiction().intro()
        b, pb = get_example(ex, 'B')
        bnn, pb = pb.split()
        g.exact(contr(bnn, forall_elim(assump, X = 'B')(and_intro(bnn, pb)).rw(an)))
    nex = g.last_proven
    g.rw(an)
    g.exact(nexists_to_unique_null(nex))
    ann = g.get_last_output()
    g.app(unique_value)
    g.exact(assump)
    g.exact(and_intro(ann, pa))

with g.goal("let(A, x : BODY(x)) = take(x : require x = A; BODY(x))"):
    g.rw(co.let, position = [0]).rw(co.take, position = [1])
    g.app(eq_symm).app(g.last_proven)
    with g.subgoal():
        g.introv()
        ex = g.intro()
        nnx, ex = ex.split()
        y, px = get_example(ex)
        ya = g.cases("Y = A")
        g.exact(px.rw(req_true(ya)).rw(ya))
        nya = g.get_last_output()
        nx = px.rw(req_false(nya))
        g.app(axiom.false(contr(nnx, nx)))
    with g.subgoal():
        g.app(exists_intro(X = 'A'))
        g.rw(req_true(axiom.eq_refl))
        g.app(axiom.eq_refl)

env.tactics.register("typing", axiom.in_is_bool)
env.tactics.register("typing", axiom.is_Set_is_bool)
env.tactics.register("typing", axiom.is_Fun_is_bool)

let_is_take = g.last_proven
def_in_set_eq = equiv_is_eq(axiom.def_in_set)

with g.goal("X in A => X is_sane"):
    x_in_a = g.intro()
    a_is_set = axiom.only_in_set(x_in_a)
    x_in_set = x_in_a.rw(axiom.set_repr(a_is_set).symm)
    g.exact(x_in_set.rw(def_in_set_eq).split()[0])
element_is_sane = g.last_proven

with g.goal("A is_sane => A is_Set => A in sets"):
    a_sane, a_set = g.intros()
    g.rw(co.sets).rw(def_in_set_eq)
    g.exact(and_intro(a_sane, a_set))
sane_set_in_sets = g.last_proven

with g.goal("A is_Set => B is_Set => forall(x : (x in A => x in B) && (x in B => x in A)) => A = B"):
    a_set, b_set, assump = g.intros()
    g.rw(axiom.set_repr(a_set).symm)
    g.rw(axiom.set_repr(b_set).symm)
    g.app(axiom.set_ext).introv()
    g.app(bool_eq_by_equiv)
    impl1, impl2 = forall_elim(assump, X = 'X').split()
    g.exact(impl1)
    g.exact(impl2)
set_ext2 = g.last_proven

with g.goal("B is_sane => A <:= B => A is_sane"):
    b_sane, ab = g.intros()
    ab = ab.rw(co._subset_eq)
    a_set, ab = ab.split()
    b_set, ab = ab.split()
    b_in_sets = sane_set_in_sets(b_sane, b_set)
    with g.goal("A = map_set(x : require x in A ; x, B)"):
        g.app(set_ext2(a_set))
        g.rw(co['map_set',1,0]).rw(req_true(b_set)).app(axiom.set_is_set)
        g.introv('X')
        g.cases()
        with g.subgoal():
            x_in_a = g.intro()
            g.rw(co['map_set',1,0]).rw(req_true(b_set)).rw(def_in_set_eq)
            g.cases().exact(element_is_sane(x_in_a))
            g.app(exists_intro(X = 'X'))
            x_in_b = forall_elim(ab, X = 'X')(x_in_a)
            g.rw(req_true(x_in_a)).rw(req_true(x_in_b))
            g.app(axiom.eq_refl)
        with g.subgoal():
            x_in_ms = g.intro()
            x = x_in_ms.rw(co['map_set',1,0]).rw(req_true(b_set))
            x = x.rw(def_in_set_eq)
            x_sane, x = x.split()
            _, x = get_example(x, 'X2')
            _, x = x.split()
            with g.goal("X2 in A"):
                x_nin_a = g.by_contradiction().intro()
                x2 = x.rw(req_false(x_nin_a))
                x2 = axiom.null_is_not_sane.rw(x2.symm)
                g.exact(contr(x2, x_sane))
            x2_in_a = g.last_proven
            x = x.rw(req_true(x2_in_a))
            g.exact(x2_in_a.rw(x.symm))
    g.rw(g.last_proven.freeze('A'))
    g.app(element_is_sane(axiom.replacement(b_in_sets)))

subset_of_sane_is_sane = g.last_proven

with g.goal("f in funcs => image(f) != powerset(domain(f))"):
    f_fun = g.intro()
    f_sane, f_Fun = f_fun.rw(co.funcs).rw(def_in_set_eq).split()

    c_def = local_def("C = set(x : x in domain(f) && x !in f[x] )")
    g.app(neq_by_pred(PRED = "x : C !in x").freeze('C'))
    with g.subgoal():
        c_in_img = g.by_contradiction().intro()
        c_in_img = c_in_img.rw(co.image).rw(co['map_set',0,0]).rw(co['map_set',1,0])
        c_in_img = c_in_img.rw(req_true(f_Fun))
        with g.goal("domain(f) is_Set"):
            g.rw(co.domain).rw(req_true(f_Fun))
            g.app(axiom.set_is_set)
        c_in_img = c_in_img.rw(req_true(g.last_proven))
        _,c_in_img = c_in_img.rw(def_in_set_eq).split()
        _,c_in_img = get_example(c_in_img)
        x_in_domain, c_in_img = c_in_img.split()
        x_in_c = g.cases("X in C")
        with g.subgoal():
            _,x = x_in_c.rw(c_def).rw(def_in_set_eq).split()
            _,x = x.split()
            g.exact(contr(x, x_in_c.rw(c_in_img)))
        x_nin_c = g.get_last_output()
        with g.subgoal():
            g.app(contr(x_nin_c))
            g.rw(c_def).rw(def_in_set_eq).cases()
            g.exact(element_is_sane(x_in_domain))
            g.cases().exact(x_in_domain)
            g.exact(x_nin_c.rw(c_in_img))
    with g.subgoal():
        g.app(dneg_rev).rw(co.powerset)
        with g.goal("domain(f) is_Set"):
            g.rw(co.domain)
            g.rw(req_true(f_Fun))
            g.app(axiom.set_is_set)
        domain_is_set = g.last_proven
        g.rw(req_true(g.last_proven))
        g.rw(def_in_set_eq)
        g.cases()
        with g.subgoal(node = g.all_goals[1]):
            g.rw(co._subset_eq)
            g.cases().rw(c_def).app(axiom.set_is_set)
            g.cases().exact(domain_is_set)
            g.introv()
            x = g.intro()
            x = x.rw(c_def).rw(def_in_set_eq)
            x = x.split()[1].split()[0]
            g.exact(x)
        g.app(subset_of_sane_is_sane(0, g.last_proven))
        g.exact(axiom.fun_sane(f_Fun, f_sane))

print("Cantor diagonal:")
print(g.last_proven)
