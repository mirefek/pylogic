from logic_env import LogicEnv
from tactics import apply_spec, Intros, PatternLookupGoal, ApplyExact
from term import Term, TermFunction, get_unused_name
from pytheorem import Theorem
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

by_contradiction = axiom.double_neg.rw(co._neg, position=[0])
print("by contradiction", by_contradiction)

with g.goal("(!X => X) => X"):
    a = g.intros()
    nx = g.app(axiom.double_neg).rw(co._neg).intros()
    g.exact(contr(nx, a(nx)))

assump_neg = g.last_proven
print("assump_neg:", assump_neg)

with g.goal("(A => X) => (!A => X) => X"):
    ax, nax = g.intros()
    g.app(by_contradiction)
    nx = g.intro().rw(co._neg)
    na = chain(ax,nx)
    na = na.rw(env.definitions[co._neg].symm())
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
    na = g.app(by_contradiction).intro()
    g.app(assump)
    g.choose0().assumed()

split_and1 = g.last_proven
print("split_and1:", split_and1)

with g.goal("A && B => B"):
    g.rw(co._and).rw(co._neg)
    assump = g.intro()
    nb = g.app(by_contradiction).intro()
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

cases_and = g.last_proven
print("cases_and:", cases_and)
env.tactics.register("cases_goal", cases_and)

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
thm_not_false = x.rw(env.definitions[co._neg].symm)
thm_true = thm_not_false.rw(env.definitions[co.true].symm)

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

bool_eq_by_equiv = g.last_proven

env.tactics.register("typing", axiom.eq_is_bool)
env.tactics.register("typing", axiom.impl_is_bool)
with g.goal("false is_bool"):
    g.rw(co._is_bool)
    g.choose0().app(axiom.eq_refl)
env.tactics.register("typing", g.last_proven)

def prove_basic_typing(term):
    with g.goal(term):
        c = g.current_goal.term.args[0].f
        g.rw(c)
        g.typing()
    env.tactics.register("typing", g.last_proven)

prove_basic_typing("!X is_bool")
prove_basic_typing("true is_bool")
prove_basic_typing("(X || Y) is_bool")
prove_basic_typing("(X && Y) is_bool")
prove_basic_typing("(X ^^ Y) is_bool")
prove_basic_typing("(X <=> Y) is_bool")
prove_basic_typing("to_bool(X) is_bool")
prove_basic_typing("to_bool1(X) is_bool")
prove_basic_typing("exists(x : PRED(x)) is_bool")
prove_basic_typing("forall(x : PRED(x)) is_bool")

strip_to_bool = axiom.double_neg.rw(env.definitions[co.to_bool].symm)
intro_to_bool = dneg_rev.rw(env.definitions[co.to_bool].symm)

with g.goal("X is_bool => to_bool(X) = X"):
    g.intro()
    g.app(bool_eq_by_equiv)
    g.typing()   # to_bool(X) is_bool
    g.assumed()  # X is_bool
    g.exact(strip_to_bool)  # to_bool(X) => X
    g.exact(intro_to_bool)    # X => to_bool(X)

is_bool_to_bool_eq = g.last_proven

with g.goal("X is_bool => X => X = true"):
    xb, x = g.intros()
    g.app(bool_eq_by_equiv)
    g.exact(xb)  # X is_bool
    g.typing()   # true is_bool
    g.intro()    # X => true
    g.app(thm_true)
    g.intro()    # true => X
    g.exact(x)

to_eq_true = g.last_proven

with g.goal("X is_bool => !X => X = false"):
    xb, nx = g.intros()
    g.app(bool_eq_by_equiv)
    g.exact(xb)           # to_bool(X) is_bool
    g.typing()            # false is_bool
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
    with g.goal(Term(co._is_bool, (term,))):
        g.typing()
    return rule(g.last_proven, thm)

autoconvert = dict()
autoconvert["reduce"] = PatternLookupRewrite()
def add_autoconvert(thm, c, i):
    autoconvert[c,i] = thm
    autoconvert["reduce"] = autoconvert["reduce"].add_rule(thm.symm)

with g.goal("(A => B) = (A => to_bool(B))"):
    g.app(bool_eq_by_equiv).typing().typing()
    ab,a = g.intros()
    g.exact(intro_to_bool(ab(a)))
    abb,a = g.intros()
    g.exact(strip_to_bool(abb(a)))

add_autoconvert(g.last_proven, co._impl, 1)

with g.goal("(A => B) = (to_bool(A) => B)"):
    g.app(bool_eq_by_equiv).typing().typing()
    ab,aa = g.intros()
    g.exact(ab(strip_to_bool(aa)))
    aab,a = g.intros()
    g.exact(aab(intro_to_bool(a)))

add_autoconvert(g.last_proven, co._impl, 0)

def prove_autoconvert_by_definition(constant, *ii):
    for i in ii:
        c_def = env.definitions[constant]
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
        g.rw(axiom.if_true(intro_to_bool(c)))
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
exists_elim = env.definitions[co.exists].to_impl().rw(autoconvert["reduce"])

print(exists_intro) # PRED(X) => exists(x : PRED(x))
print(exists_elim)  # exists(x : PRED(x)) => PRED(example(x : PRED(x)))
eq_symm = env.rewriter._eq_symm

with g.goal("(X = Y) = (Y = X)"):
    g.app(bool_eq_by_equiv).typing().typing()
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
    g.app(bool_eq_by_equiv).typing().typing()
    g.intro()
    g.exact(thm_true)
    g.intros()
    g.exact(thm_true)

add_bool_calc(g.last_proven)
add_bool_calc(env.definitions[co._neg].symm) # (X => false) = !X

with g.goal("(true => X) = X"):
    g.app(bool_eq_by_equiv).typing()
    g.postpone("typing")
    tx = g.intro()
    g.exact(tx(thm_true))
    x,_ = g.intros()
    g.exact(x)

add_bool_calc(g.last_proven)

with g.goal("(false => X) = true"):
    g.app(bool_eq_by_equiv).typing().typing()
    g.intros()
    g.exact(thm_true)
    g.intro()
    g.app(axiom.false,0)

add_bool_calc(g.last_proven)
add_bool_calc(env.definitions[co.true].symm)

with g.goal("!!X = X"):
    g.app(bool_eq_by_equiv).typing()
    g.postpone("typing")
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
    x_bool = env.hypothesis("typing", "X is_bool")
    x_sane = axiom.bool_is_sane(x_bool)
    xnn = neq_by_pred(PRED = "x : x is_sane")(x_sane, axiom.null_is_not_sane)
    g.rw(to_eq(xnn)).rw(bool_calc).app(axiom.eq_refl)

    root = g.current_ctx.tree.root

print(g.last_proven)
to_bool1_idemp = g.last_proven

with g.goal("(!A => B) => (!B => A)"):
    nab,nb = g.intros()
    na = g.app(by_contradiction).intro()
    g.exact(contr(nb, nab(na)))

nimpl_symm = g.last_proven
x = nimpl_symm(B = "!B")
x = x.rw(env.definitions[co.to_bool].symm)
x = x.rw(autoconvert["reduce"])
contraposition = x
x = x(A = "!A")
x = x.rw(env.definitions[co.to_bool].symm)
x = x.rw(autoconvert["reduce"])
impln_symm = x
x = x(B = "!B")
x = x.rw(env.definitions[co.to_bool].symm)
x = x.rw(autoconvert["reduce"])
contraposition_rev = x

x = exists_intro(PRED = "x : !to_bool1(PRED(x))")
x = nimpl_symm(x)
x = x.rw(env.definitions[co.forall].symm)
forall_elim = x

x = exists_elim(PRED = "x : !to_bool1(PRED(x))")
x = impln_symm(x)
x = x.rw(env.definitions[co.forall].symm)
forall_intro_full = x

with g.goal("X => to_bool1(X)"):
    g.rw(co.to_bool1)
    g.app(or_intro2, 0)

to_bool1_intro = g.last_proven
forall_intro = chain(to_bool1_intro, forall_intro_full)
print(forall_intro)

x = forall_elim(PRED = "x : BODY1(x) = BODY2(x)").rw(to_bool1_idemp)
with g.goal(x.term):
    g.app_exact(x(typing = 0), 1)
    g.typing()
forall_eq_elim = g.last_proven # x(typing = g.last_proven)
x = forall_elim(PRED = "x : forall(y : PRED(x,y))").rw(to_bool1_idemp)
with g.goal(x.term):
    g.app_exact(x(typing = 0), 1)
    g.typing()
forall_forall_elim = g.last_proven # x(typing = g.last_proven)

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
prove_extensionality_by_definition(co.unique)
prove_extensionality_by_definition(co.take)
prove_extensionality_by_definition(co.let)
