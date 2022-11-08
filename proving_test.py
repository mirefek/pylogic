from logic_env import LogicEnv
from tactics import apply_spec, Intros, PatternLookupGoal, ApplyExact, BasicTactic
from term import Term, TermVariable, get_unused_name
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

dneg_intro = g.last_proven

with g.goal("(A => B) => (B => C) => (A => C)"):
    ab, bc, a = g.intros()
    g.exact(bc(ab(a)))

chain = g.last_proven

with g.goal("!X => X => false"):
    nx, x = g.intros()
    g.exact(nx.rw(co._neg)(x))

contr = g.last_proven
print(contr)

x = env.basic_impl.refl(env.to_term("false"))
thm_not_false = x.rw(co._neg.def_thm.symm)
thm_true = thm_not_false.rw(co.true.def_thm.symm)

env.tactics.register("by_contradiction", co._neg.def_thm.symm.to_impl())

with g.goal("X is_bool => !!X => X"):
    x_bool, nnx = g.intros()
    x_bool = x_bool.rw(co._is_bool).rw(co._or)
    with g.goal("X != false", unfreeze = False):
        xf = g.by_contradiction().intro()
        g.app(contr(nnx))
        g.rw(xf).exact(thm_not_false)
    g.rw(x_bool(g.last_proven)).exact(thm_true)
dneg_elim = g.last_proven

with g.goal("B => A => A"):
    b = g.intro()
    g.app(dneg_elim)
    g.app(axiom.impl_is_bool)
    naa = g.by_contradiction().intro()
    aaf = contr(naa)
    f = aaf(env.basic_impl._impl_refl)
    g.exact(axiom.false(f, X = "B => false")(b))
dummy_assump = g.last_proven(1,0)

# proved without the necessity of using the axiom
# well implication reflexivity was used during the proof
# but that can be also directly obtained from equality congruence
print(dummy_assump)

with g.goal("!!X => X"):
    g.app(dneg_elim)
    g.app(axiom.impl_is_bool)
    assump = contr(g.by_contradiction().intro())
    nnx = g.app(assump).intro()
    g.app(axiom.false).app(contr(nnx))
    x = g.by_contradiction().intro()
    g.app(assump).intro()
    g.exact(x)
dneg_elim = g.last_proven

env.tactics.register("by_contradiction", dneg_elim.rw(co._neg, position=[0]))
env.tactics.register("symm", env.rewriter._eq_symm)

with g.goal("(!X => X) => X"):
    a = g.intros()
    nx = g.app(dneg_elim).rw(co._neg).intros()
    g.exact(contr(nx, a(nx)))

assump_neg = g.last_proven
print("assump_neg:", assump_neg)

with g.goal("(A => X) => (!A => X) => X"):
    ax, nax = g.intros()
    g.by_contradiction()
    nx = g.intro().rw(co._neg)
    na = chain(ax,nx)
    na = na.rw(co._neg.def_thm.symm)
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

env.add_impl_rule("split", split_and1, split_and2)

with g.goal("A => B => A && B"):
    g.rw(co._and).rw(co._neg)
    a,b,ab = g.intros()
    g.app(cases_or(ab))
    g.exact(contr(0,a))
    g.exact(contr(0,b))

and_intro = g.last_proven
print("and_intro:", and_intro)
env.tactics.register("cases_goal", and_intro)

with g.goal("!(A => B) => A"):
    nab = g.intro()
    na = g.by_contradiction().intro()
    g.app(contr(nab))
    a = g.intro()
    g.app(axiom.false)
    g.exact(contr(na, a))
nimpl_elim1 = g.last_proven

with g.goal("!(A => B) => !B"):
    nab = g.intro()
    b = g.by_contradiction().intro()
    g.app(contr(nab))
    a = g.intro()
    g.exact(b)
nimpl_elim2 = g.last_proven

env.add_impl_rule("split", nimpl_elim1, nimpl_elim2)

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

with g.goal("(!A => (A => B) => B) => (A => B) => B"):
    naabb, ab = g.intros()
    a = g.cases('A')
    g.exact(ab(a))
    na = g.get_last_output()
    g.exact(naabb(na, ab))
wlog = g.last_proven
print("WLOG:", wlog)

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

to_bool_elim = dneg_elim.rw(co.to_bool.def_thm.symm)
to_bool_intro = dneg_intro.rw(co.to_bool.def_thm.symm)

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
        header, _ = env.split_eq(constant.def_thm.term)
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
        g.exact(dneg_intro(nc))
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
exists_elim = co.exists.def_thm.to_impl().rw(autoconvert["reduce"])

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
add_bool_calc(co._neg.def_thm.symm) # (X => false) = !X

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
add_bool_calc(co.true.def_thm.symm)

with g.goal("!!X = X"):
    g.app(bool_eq_by_equiv)
    g.exact(dneg_elim).exact(dneg_intro)

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

with g.goal("X is_sane => X != null"):
    x = g.intro()
    x = x.rw(g.by_contradiction().intro())
    g.exact(contr(axiom.null_is_not_sane, x))
sane_to_not_null = g.last_proven

with g.goal("to_bool1(X) = X"):
    g.rw(co.to_bool1)
    x_sane = axiom.bool_is_sane.set_resolver(TypingResolver(env), "typing2")
    xnn = sane_to_not_null(x_sane)
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
x = x.rw(co.to_bool.def_thm.symm)
x = x.rw(autoconvert["reduce"])
contraposition = x
x = x(A = "!A")
x = x.rw(co.to_bool.def_thm.symm)
x = x.rw(autoconvert["reduce"])
impln_symm = x
x = x(B = "!B")
x = x.rw(co.to_bool.def_thm.symm)
x = x.rw(autoconvert["reduce"])
contraposition_rev = x

null_to_false = chain(to_bool_intro, axiom.null_to_bool.to_impl())
null_to_any = chain(null_to_false, axiom.false)
req_true = axiom.if_true(B = "null").rw(co._require.def_thm.symm)
req_false = axiom.if_false(B = "null").rw(co._require.def_thm.symm)

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

#  (require C; A) != null => C
req_nn_to_C = nimpl_symm(req_false)
#  (require C; A) != null => (require C; A) = A
req_nn_simp = chain(req_nn_to_C, req_true)(B = 'A')
with g.goal("(require C; A) != null => A != null"):
    assump = g.intro()
    g.exact(assump.rw(req_nn_simp(assump)))
req_nn_nn = g.last_proven

with g.goal("to_bool1(require C; A) => C => to_bool1(A)"):
    rca, c = g.intros()
    g.exact(rca.rw(req_true(c)))
to_bool1_req_elim = g.last_proven
env.add_impl_rule("to_impl", to_bool1_req_elim)

with g.goal("(C => to_bool1(A)) => to_bool1(require C; A)"):
    ca = g.intro()
    c = g.cases('C')
    g.rw(req_true(c)).exact(ca(c))
    nc = g.get_last_output()
    g.rw(req_false(nc)).rw(co.to_bool1)
    g.choose0().app(axiom.eq_refl)
to_bool1_req_intro = g.last_proven

x = exists_intro(PRED = "x : !to_bool1(PRED(x))")
x = nimpl_symm(x)
x = x.rw(co.forall.def_thm.symm)
forall_elim_full = x

x = exists_elim(PRED = "x : !to_bool1(PRED(x))")
x = impln_symm(x)
x = x.rw(co.forall.def_thm.symm)
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

def generalize(thm, v, full = False):
    if isinstance(v, str):
        v = env.parser.get_var(v, 0)
    pred = thm.term
    if full:
        assert pred.f == co.to_bool1
        pred = pred.args[0]
    pred = pred.substitute_free({ v : Term(1) })
    x = Term(co.to_bool1, (pred,))
    x = Term(co._neg, (x,))
    x = Term(co.example, (x,), (['x'],))
    example = x
    thm = thm.specialize({ v : example })
    if full:
        x = forall_intro_full(PRED = pred)
    else:
        x = forall_intro(PRED = pred)
    x = x.modus_ponens_basic(thm)
    return x

env.generalize = generalize

with g.goal("forall(x : PRED(x) = PRED2(x)) => example(x : PRED(x)) = example(x : PRED2(x))"):
    assump = g.intro()
    ex = g.cases("PRED(example(x : PRED2(x)))")
    assump_eq = forall_eq_elim(assump)
    with g.subgoal():
        g.app(axiom.example_well_ordered)
        with g.goal("PRED(X) => PRED2(X)"):
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
                TermVariable(numb2, "A"),
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

        assert isinstance(v, TermVariable) and v.arity == 0
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

def get_example(thm, v = None, v2 = None, label = "_SUBST_", with_def_eq = False):
    assert thm.term.f in (env.constants.exists, env.constants.exists_uq)
    get_uq = (thm.term.f == env.constants.exists_uq)
    # find the right variable v
    if v is None:
        [[v]] = thm.term.bound_names
        v = v.upper()
    if isinstance(v, str):
        v = env.parser.get_var(v,0)
    if v in thm.term.free_vars:
        v = env.get_locally_fresh_var(v, set(x.name for x in thm.term.free_vars))
    # find the right variable v2
    if get_uq:
        if v2 is None: v2 = v.name
        if isinstance(v2, str):
            v2 = env.parser.get_var(v2,0)
        if v2 in thm.term.free_vars or v2 == v:
            used_names = set(x.name for x in thm.term.free_vars)
            used_names.add(v.name)
            v2 = env.get_locally_fresh_var(v2, used_names)
    if isinstance(label, str):
        label = AssumptionLabel(label)
    if get_uq:
        thm = exists_uq_elim_eq(thm, A = v.to_term(), B = v2.to_term())
    else:
        thm = exists_elim_eq(thm, A = v.to_term())
    assert label not in thm.assump_labels()
    thm = thm.set_resolver(SubstResolver(env), label)
    thm = thm.freeze(thm.assumption(label).free_vars)
    if with_def_eq:
        def_eq = env.hypothesis(label, thm.assumption(label))
    if get_uq:
        if with_def_eq:
            return thm.split()+(def_eq,)
        else:
            return thm.split()
    else:
        if with_def_eq:
            thm, def_eq
        else:
            return thm

def local_def(term, label = "_EQ_"):
    term = env.to_term(term)
    v, body = env.split_eq(term)
    v = v.f
    assert isinstance(v, TermVariable)
    assert v.arity == 0
    assert v not in body.free_vars
    if isinstance(label, str): label = AssumptionLabel(label)
    res = env.hypothesis(label, term, frozen = True)
    res = res.set_resolver(SubstResolver(env), label)
    return res

class IntroVar(BasicTactic):
    def get_subgoals(self, v = None, full = False):
        self.full = full
        assert self.goal.f == self.env.constants.forall
        if v is None:
            [[v]] = self.goal.bound_names
            v = v.upper()
        if isinstance(v, str):
            v = self.env.parser.get_var(v,0)
        if v in self.goal.free_vars:
            v = self.env.get_locally_fresh_var(v, set(x.name for x in self.goal.free_vars))
        self.v = v
        subgoal = self.goal.args[0].substitute_bvars([v.to_term()])
        if full: subgoal = Term(co.to_bool1, (subgoal,))
        return [subgoal]
    def build_thm(self, thm):
        return thm.generalize(self.v, full = self.full)

env.tactics.register("introv", IntroVar)

with g.goal("exists_uq(x : PRED(x)) => exists(x : PRED(x))"):
    assump = g.intro()
    assump = assump.rw(co.exists_uq)
    assump = get_example(assump)
    a1, a2 = assump.split()
    g.exact(exists_intro.modus_ponens_basic(a1))

exists_uq_to_exists = g.last_proven

with g.goal("exists_uq(x : PRED(x)) => PRED(A) => PRED(B) => A = B"):
    ex_uq, pred_a, pred_b = g.intros()
    ex_uq = ex_uq.rw(co.exists_uq)
    assump = get_example(ex_uq, 'X')
    pred_x, uq = assump.split()
    uq = forall_elim(uq)
    g.exact(uq(pred_a).rw(uq(pred_b).symm))
exists_uq_is_uq = g.last_proven

with g.goal("exists_uq(x : PRED(x)) => PRED(unique(x : PRED(x)))"):
    ex_uq = g.intro()
    g.rw(co.unique).rw(req_true(ex_uq))
    ex = exists_uq_to_exists(ex_uq)
    g.exact(exists_elim(ex))
exists_uq_unique = g.last_proven    

with g.goal("unique(x : PRED(x)) != null => exists_uq(x : PRED(x))"):
    x = g.intro().rw(co.unique)
    g.exact(req_nn_to_C(x))
unique_nn_to_exists_uq = g.last_proven

with g.goal("exists_uq(x : PRED(x)) => A = unique(x : PRED(x)) => (PRED(A) && (PRED(B) => B = A))"):
    ex_uq, a_def = g.intros()
    g.cases()
    with g.subgoal("PRED(A)"):
        g.rw(a_def)
        g.exact(exists_uq_unique(ex_uq))
    pred_a = g.last_proven
    pred_b = g.intro()
    g.exact(exists_uq_is_uq(ex_uq, pred_b, pred_a))
exists_uq_elim_eq = g.last_proven

with g.goal("!exists_uq(x : PRED(x)) => unique(x : PRED(x)) = null"):
    nex_uq = g.intro()
    g.rw(co.unique)
    g.app(req_false(nex_uq))
nexists_uq_to_unique_null = g.last_proven

#    !exists(x : PRED(x)) => unique(x : PRED(x)) = null
nexists_to_unique_null = chain(contraposition_rev(exists_uq_to_exists), nexists_uq_to_unique_null)

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

with g.goal("!exists_uq(x : A)"):
    ex_uq = g.by_contradiction().intro()
    a, uq = get_example(ex_uq)
    eq = uq(a)
    eq = eq.rw(eq.symm(Y = 'Z'))
    x = neq_by_pred(PRED = 'x:x', X = 'true', Y = 'false')
    x = x(thm_true, thm_not_false)
    g.exact(contr(x, eq))
universal_not_uq = g.last_proven

with g.goal("forall(x : x != null && PRED(x) => x = A) => PRED(A) => unique(x : x != null && PRED(x)) = A"):
    assump, pa = g.intros()
    an = g.cases("A = null")
    with g.goal("!exists(x : x != null && PRED(x))"):
        ex = g.by_contradiction().intro()
        pb = get_example(ex, 'B')
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
        px = get_example(ex)
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

env.rewriter.add_extensionality(axiom.set_ext)
env.rewriter.add_extensionality(axiom.fun_ext)

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
set_eq_intro = g.last_proven

with g.goal("A <:= B => X in A => X in B"):
    ab = g.intro()
    ab = ab.rw(co._subset_eq).split()[1].split()[1]
    ab = forall_elim(ab)
    g.exact(ab)
subset_to_in_impl = g.last_proven

with g.goal("A is_Set => B is_Set => A \ B is_Set"):
    a_set, b_set = g.intros()
    g.rw(co._setdiff)
    g.rw(req_true(a_set)).rw(req_true(b_set))
    g.app(axiom.set_is_set)
setdiff_is_set = g.last_proven

with g.goal("B is_Set => X in A => X !in A \ B => X in B"):
    b_set, xa, xnab = g.intros()
    x_sane = element_is_sane(xa)
    a_set = axiom.only_in_set(xa)
    xnab = xnab.rw(co._setdiff)
    xnab = xnab.rw(req_true(a_set)).rw(req_true(b_set))
    xnab = xnab.rw(def_in_set_eq)
    xnb = g.by_contradiction().intro()
    g.app(contr(xnab))
    g.cases().exact(x_sane)
    g.cases().exact(xa)
    g.exact(xnb)
avoiding_setdiff = g.last_proven

with g.goal("B is_Set => X in A => X !in B => X in A \ B"):
    b_set, xa = g.intros(2)
    g.app(nimpl_symm(avoiding_setdiff(b_set, xa)), 0)
in_setdiff_intro = g.last_proven

with g.goal("X in A \ B => (X in A && X !in B)"):
    x = g.intro().rw(co._setdiff)
    ab_set = axiom.only_in_set(x)
    abnn = axiom.set_not_null(ab_set)
    a_set = req_nn_to_C(abnn)
    abnn = req_nn_nn(abnn)
    b_set = req_nn_to_C(abnn)
    x = x.rw(req_true(a_set)).rw(req_true(b_set))
    x = x.rw(def_in_set_eq)
    x_sane, x = x.split()
    xa,xnb = x.split()
    g.exact(and_intro(xa, xnb))
in_setdiff_elim = g.last_proven

with g.goal("A is_Set => B is_Set => A \ B <:= A"):
    a_set, b_set = g.intros()
    g.rw(co._subset_eq)
    g.cases().exact(setdiff_is_set(a_set, b_set))
    g.cases().exact(a_set)
    xab = g.introv('X').intro()
    g.exact(in_setdiff_elim(xab).split()[0])
setdiff_is_subset = g.last_proven

with g.goal("f is_Fun => domain(f) is_Set"):
    f_fun = g.intro()
    g.rw(co.domain)
    g.rw(req_true(f_fun))
    g.app(axiom.set_is_set)
domain_is_set = g.last_proven

with g.goal("A is_Set => map_set(x : BODY(x), A) is_Set"):
    a_set = g.intro()
    g.rw(co['map_set',1,0]).rw(req_true(a_set)).app(axiom.set_is_set)
map_set_BODY_is_set = g.last_proven

with g.goal("f is_Fun => A is_Set => map_set(f, A) is_Set"):
    f_fun, a_set = g.intros()
    g.rw(co['map_set',0,0]).rw(req_true(f_fun)).app(map_set_BODY_is_set(a_set))
map_set_is_set = g.last_proven

with g.goal("f is_Fun => image(f) is_Set"):
    f_fun = g.intro()
    g.rw(co.image)
    g.exact(map_set_is_set(f_fun, domain_is_set(f_fun)))
image_is_set = g.last_proven

with g.goal("(X in require C; A) => X in A"):
    x_in_r = g.intro()
    x = axiom.only_in_set(x_in_r)
    x = axiom.set_not_null(x)
    g.exact(x_in_r.rw(req_nn_simp(x)))
in_req_simp = g.last_proven

with g.goal("Y in map_set(x : BODY(x), A) => exists(x : require x in A; Y = BODY(x) )"):
    x = g.intro()
    x = x.rw(co['map_set',1,0])
    x = in_req_simp(x)
    x = def_in_set_eq(x).split()[1]
    g.exact(x)
in_map_set_BODY_elim = g.last_proven

with g.goal("Y is_sane => exists(x : require x in A; Y = BODY(x) ) => Y in map_set(x : BODY(x), A)"):
    y_sane, ex = g.intros()
    a_set = axiom.only_in_set(get_example(ex).split()[0])
    g.rw(co['map_set',1,0]).rw(req_true(a_set)).rw(def_in_set_eq)
    g.cases().exact(y_sane)
    g.exact(ex)
in_map_set_BODY_intro_raw = g.last_proven

with g.goal("Y is_sane => X in A => Y = BODY(X) => Y in map_set(x : BODY(x), A)"):
    y_sane, x_in_a, y_is_bx = g.intros()
    g.app(in_map_set_BODY_intro_raw)
    g.app(y_sane).app(exists_intro(X = 'X'))
    g.rw(req_true(x_in_a)).exact(y_is_bx)
in_map_set_BODY_intro = g.last_proven

with g.goal("B is_sane => A <:= B => A is_sane"):
    b_sane, ab = g.intros()
    ab = ab.rw(co._subset_eq)
    a_set, ab = ab.split()
    b_set, ab = ab.split()
    b_in_sets = sane_set_in_sets(b_sane, b_set)
    map_set_b_is_set = map_set_BODY_is_set(b_set)
    with g.goal("A = map_set(x : require x in A ; x, B)"):
        g.app(set_eq_intro(a_set))
        g.app(map_set_b_is_set)
        g.introv('X')
        g.cases()
        with g.subgoal():
            x_in_a = g.intro()
            g.app(in_map_set_BODY_intro_raw)
            g.exact(element_is_sane(x_in_a))
            g.app(exists_intro(X = 'X'))
            x_in_b = forall_elim(ab, X = 'X')(x_in_a)
            g.rw(req_true(x_in_a)).rw(req_true(x_in_b))
            g.app(axiom.eq_refl)
        with g.subgoal():
            x_in_ms = g.intro()
            x_sane = element_is_sane(x_in_ms)
            x = in_map_set_BODY_elim(x_in_ms)
            x = get_example(x, 'X2')
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

with g.goal("f[X] != null => f is_Fun"):
    fxnn = g.intro()
    f_fun = g.cases(axiom.only_apply_fun)
    g.exact(f_fun)
    fxn = g.get_last_output()
    g.app(axiom.false(contr(fxnn, fxn)))
applied_is_fun = g.last_proven

with g.goal("X is_sane => X = Y => X = req_sane(Y)"):
    x_sane, xy = g.intros()
    g.rw(co.req_sane).rw(xy.symm).rw(req_true(x_sane))
    g.exact(xy)
eq_req_sane_intro = g.last_proven

with g.goal("f[X] != null => (X is_sane && f[X] is_sane)"):
    x = g.intro()
    x = x.rw(axiom.fun_repr(applied_is_fun(x)).symm)
    x = x.rw(axiom.def_apply_fun)
    g.cases()
    g.exact(req_nn_to_C(x))
    x = req_nn_nn(x)
    x = x.rw(co.req_sane)
    x = req_nn_to_C(x)
    g.exact(x)
argument_value_is_sane = g.last_proven
x = argument_value_is_sane.impl_to_labels("fxnn")
argument_is_sane, value_is_sane = x.split()
argument_is_sane = argument_is_sane.labels_to_impl("fxnn")
value_is_sane = value_is_sane.labels_to_impl("fxnn")    

with g.goal("fun(x : BODY(x))[X] != null => fun(x : BODY(x))[X] = BODY(X)"):
    x = g.intro()
    x = x.rw(axiom.def_apply_fun)
    g.rw(axiom.def_apply_fun)
    x_sane = req_nn_to_C(x)
    x = req_nn_nn(x)
    g.rw(req_true(x_sane))
    x = x.rw(co.req_sane)
    g.rw(co.req_sane)
    val_sane = req_nn_to_C(x)
    x = req_nn_nn(x)
    g.rw(req_true(val_sane))
    g.app(axiom.eq_refl)
def_apply_fun_nn = g.last_proven

with g.goal("Y in map_set(f, A) => exists(x : require x in A; Y = f[x])"):
    x = g.intro()
    x = x.rw(co['map_set',0,0])
    x = in_req_simp(x)
    x = in_map_set_BODY_elim(x)
    g.exact(x)
in_map_set_elim = g.last_proven

with g.goal("Y != null => X in A => Y = f[X] => Y in map_set(f, A)"):
    ynn, x_in_a, y_fx = g.intros()
    g.rw(co['map_set',0,0])
    y_sane = value_is_sane(ynn.rw(y_fx)).rw(y_fx.symm)
    fxnn = sane_to_not_null(y_sane).rw(y_fx)
    f_fun = applied_is_fun(fxnn)
    g.rw(req_true(f_fun)).app(in_map_set_BODY_intro)
    g.exact(y_sane)
    g.exact(x_in_a)
    g.exact(y_fx)
in_map_set_intro = g.last_proven

with g.goal("X in domain(f) => f[X] != null"):
    x = g.intro()
    x = in_req_simp(x.rw(co.domain))
    x = def_in_set_eq(x)
    x = x.split()[1]
    g.exact(x)
in_domain_elim = g.last_proven

with g.goal("f[X] != null => X in domain(f)"):
    assump = g.intro()
    f_fun = applied_is_fun(assump)
    g.rw(co.domain).rw(req_true(f_fun))
    g.rw(def_in_set_eq)
    g.cases().exact(argument_is_sane(assump))
    g.exact(assump)
in_domain_intro = g.last_proven

with g.goal("domain(f) != null => f is_Fun"):
    x = g.intro()
    x = x.rw(co.domain)
    x = req_nn_to_C(x)
    g.exact(x)
domain_is_of_fun = g.last_proven

with g.goal("Y in image(f) => exists(x : Y = f[x])"):
    x = g.intro()
    x = x.rw(co.image)
    x = in_map_set_elim(x)
    x = get_example(x)
    _,x = x.split()
    g.app(exists_intro).exact(x)
in_image_elim = g.last_proven

with g.goal("Y != null => Y = f[X] => Y in image(f)"):
    ynn, y_fx = g.intros()
    g.rw(co.image)
    g.app(in_map_set_intro).exact(ynn)
    g.app(in_domain_intro).exact(ynn.rw(y_fx))
    g.exact(y_fx)
in_image_intro = g.last_proven

with g.goal("f[X] != null => X in domain(f)"):
    fxnn = g.intro()
    g.rw(co.domain)
    g.rw(req_true(applied_is_fun(fxnn))).rw(def_in_set_eq)
    g.cases()
    g.exact(argument_is_sane(fxnn))
    g.exact(fxnn)
argument_in_domain = g.last_proven

with g.goal("f in funs => image(f) != powerset(domain(f))"):
    f_fun = g.intro()
    f_sane, f_Fun = f_fun.rw(co.funs).rw(def_in_set_eq).split()

    c_def = local_def("C = set(x : x in domain(f) && x !in f[x] )")
    g.app(neq_by_pred(PRED = "x : C !in x").freeze('C'))
    with g.subgoal():
        c_in_img = g.by_contradiction().intro()
        cnn = sane_to_not_null(element_is_sane(c_in_img))
        c_in_img = in_image_elim(c_in_img)
        c_in_img = get_example(c_in_img)
        x_in_domain = argument_in_domain(cnn.rw(c_in_img))
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
        g.app(dneg_intro).rw(co.powerset)
        domain_f_is_set = domain_is_set(f_Fun)
        g.rw(req_true(domain_f_is_set))
        g.rw(def_in_set_eq)
        g.cases()
        with g.subgoal(node = g.all_goals[1]):
            g.rw(co._subset_eq)
            g.cases().rw(c_def).app(axiom.set_is_set)
            g.cases().exact(domain_f_is_set)
            g.introv()
            x = g.intro()
            x = x.rw(c_def).rw(def_in_set_eq)
            x = x.split()[1].split()[0]
            g.exact(x)
        g.app(subset_of_sane_is_sane(0, g.last_proven))
        g.exact(axiom.fun_sane(f_Fun, f_sane))

print("Cantor diagonal:")
print(g.last_proven)

with g.goal("f is_Fun => inverse(f) is_Fun"):
    f_fun = g.intro()
    g.rw(co.inverse).rw(req_true(f_fun)).app(axiom.fun_is_fun)
inverse_is_fun = g.last_proven

with g.goal("inverse(f) is_Fun => f is_Fun"):
    x = g.intro()
    x = axiom.fun_not_null(x.rw(co.inverse))
    x = req_nn_to_C(x)
    g.exact(x)
inverse_is_of_fun = g.last_proven

# req_sane(A) != null => req_sane(A) = A
req_sane_nn_simp = req_nn_simp(C = "A is_sane").rw(co.req_sane.def_thm.symm, repeat = True)
# req_sane(A) != null => A != null
req_sane_nn_nn = req_nn_nn(C = "A is_sane").rw(co.req_sane.def_thm.symm)

with g.goal("inverse(f) [Y] = unique(x : f[x] = Y)"):
    g.rw(co.inverse)
    f_fun = g.cases("f is_Fun")
    with g.subgoal():
        g.rw(req_true(f_fun)).rw(axiom.def_apply_fun)
        uq_null = g.cases("unique(x : f[x] = Y) = null")
        g.rw(uq_null, repeat = True).rw(co.req_sane)
        g.rw(contraposition(req_nn_nn, axiom.eq_refl), repeat = True)
        g.app(axiom.eq_refl)
        uqnn = g.get_last_output()
        label = env.to_label("uq_eq")
        fx_y, uq, def_eq = get_example(unique_nn_to_exists_uq(uqnn), 'X', 'X2', with_def_eq = True)
        g.rw(def_eq.symm, repeat = True)
        xnn = uqnn.rw(def_eq.symm)
        yn = g.cases("Y = null")
        with g.goal("f[null] = Y"):
            x = g.rw(yn).by_contradiction().intro()
            g.exact(contr(axiom.null_is_not_sane, argument_is_sane(x)))
        g.app(axiom.false)
        g.exact(contr(xnn, uq(g.last_proven).symm))
        ynn = g.get_last_output()
        fxnn = ynn.rw(fx_y.symm)
        g.rw(fx_y.symm)
        fx_sane = value_is_sane(fxnn)
        g.rw(req_true(fx_sane))
        x_sane = argument_is_sane(fxnn)
        g.rw(co.req_sane).rw(req_true(x_sane)).app(axiom.eq_refl)
    f_nfun = g.get_last_output()
    g.rw(req_false(f_nfun))
    n_nfun = impln_symm(axiom.fun_not_null, axiom.eq_refl)
    g.rw(nimpl_symm(applied_is_fun, n_nfun))
    g.rw(nimpl_symm(applied_is_fun, f_nfun))
    x = g.symm()
    g.app(nexists_uq_to_unique_null)
    g.app(universal_not_uq)
def_apply_inverse = g.last_proven

with g.goal("X in domain(inverse(f)) => f[inverse(f)[X]] = X"):
    x_in_domain = g.intro()
    x_sane = element_is_sane(x_in_domain)
    x = axiom.set_not_null(axiom.only_in_set(x_in_domain))
    x = domain_is_of_fun(x)
    f_fun = inverse_is_of_fun(x)
    x = in_domain_elim(x_in_domain)
    x = x.rw(def_apply_inverse)
    x = unique_nn_to_exists_uq(x)
    fy_x, uq, def_eq = get_example(x, 'Y', with_def_eq = True)
    g.rw(def_apply_inverse).rw(def_eq.symm)
    g.exact(fy_x)
inverse_right = g.last_proven

with g.goal("f is_injective => domain(inverse(f)) = image(f)"):
    f_fun, f_inj = g.intro().rw(co._is_injective).split()
    g.app(set_eq_intro)
    g.exact(domain_is_set(inverse_is_fun(f_fun)))
    g.exact(image_is_set(f_fun))
    g.introv('Y')
    g.cases()
    with g.subgoal():
        y_in_domain = g.intro()
        y_sane = element_is_sane(y_in_domain)
        ynn = sane_to_not_null(y_sane)
        g.app(in_image_intro(X = "inverse(f)[Y]")).exact(ynn)
        g.exact(inverse_right(y_in_domain).symm)
    with g.subgoal():
        y_in_image = g.intro()
        ynn = sane_to_not_null(element_is_sane(y_in_image))
        y_in_image = in_image_elim(y_in_image)
        g.app(in_domain_intro)
        g.rw(def_apply_inverse)
        y_fx = get_example(y_in_image, 'X')
        fxnn = ynn.rw(y_fx)
        with g.goal("unique(x : f[x] = Y) = X"):
            g.app(unique_value)
            with g.subgoal():
                g.introv('Z')
                fz_y = g.intro()
                inj = forall_elim_full(f_inj, X = 'Z')
                inj = inj(in_domain_intro(ynn.rw(fz_y.symm)))
                inj = to_bool1_idemp(inj)
                inj = forall_elim_full(inj, X = 'X')
                inj = inj(in_domain_intro(fxnn))
                inj = to_bool1_idemp(inj)
                xz = inj(fz_y.rw(y_fx))
                g.exact(xz)
            g.exact(y_fx.symm)
        g.rw(g.last_proven)
        x_sane = argument_is_sane(fxnn)
        g.exact(sane_to_not_null(x_sane))
domain_inverse = g.last_proven

with g.goal("f is_injective => f is_Fun"):
    g.exact(g.intro().rw(co._is_injective).split()[0])
injective_is_fun = g.last_proven

with g.goal("f[X] in domain(inverse(f)) => inverse(f)[f[X]] = X"):
    fx_in_domain = g.intro()
    fx_sane = element_is_sane(fx_in_domain)
    fxnn = sane_to_not_null(fx_sane)
    f_fun = applied_is_fun(fxnn)
    x = in_domain_elim(fx_in_domain)
    x = x.rw(def_apply_inverse)
    g.rw(def_apply_inverse)
    ex_uq = unique_nn_to_exists_uq(x)
    g.app(exists_uq_is_uq(ex_uq))
    g.exact(exists_uq_unique(ex_uq))
    g.app(axiom.eq_refl)
inverse_left = g.last_proven

with g.goal("f is_injective => image(inverse(f)) = domain(f)"):
    f_inj = g.intro()
    f_fun = injective_is_fun(f_inj)
    g.app(set_eq_intro)
    g.exact(image_is_set(inverse_is_fun(f_fun)))
    g.exact(domain_is_set(f_fun))
    g.introv('X').cases()
    with g.subgoal():
        x_in_img = g.intro()
        g.app(in_domain_intro)
        x_sane = element_is_sane(x_in_img)
        x_in_img = in_image_elim(x_in_img)
        x_fy = get_example(x_in_img, 'Y')
        xnn = sane_to_not_null(x_sane)
        fynn = xnn.rw(x_fy)
        y_in_domain = in_domain_intro(fynn)
        g.rw(x_fy).rw(inverse_right(y_in_domain))
        y_sane = element_is_sane(y_in_domain)
        ynn = sane_to_not_null(y_sane)
        g.exact(ynn)
    with g.subgoal():
        x_in_domain = g.intro()
        x_sane = element_is_sane(x_in_domain)        
        xnn = sane_to_not_null(x_sane)
        g.app(in_image_intro(f = "inverse(f)", X = "f[X]", Y = 'X'))
        g.app(xnn).symm()
        g.app(inverse_left)
        g.rw(domain_inverse(f_inj))
        g.app(in_image_intro)
        g.exact(in_domain_elim(x_in_domain))
        g.app(axiom.eq_refl)
image_inverse = g.last_proven

with g.goal("forall(x : true)"):
    g.introv('X', full = True)
    g.app(to_bool1_intro)
    g.exact(thm_true)

with g.goal("f is_Fun => inverse(f) is_injective"):
    f_fun = g.intro()
    g.rw(co._is_injective)
    g.cases().exact(inverse_is_fun(f_fun))
    g.introv('X', full = True)
    x_in_domain = g.app(to_bool1_req_intro).intro()
    g.app(to_bool1_intro).introv('Y', full = True)
    y_in_domain = g.app(to_bool1_req_intro).intro()
    g.app(to_bool1_intro)
    g.rw(def_apply_inverse, repeat = True)
    uq_eq = g.intro()
    uqx_nn = in_domain_elim(x_in_domain)
    uqx_nn = uqx_nn.rw(def_apply_inverse)
    ex_uq_x = unique_nn_to_exists_uq(uqx_nn)
    fa_x, _, def_eq_a = get_example(ex_uq_x, 'A', with_def_eq = True)
    g.rw(fa_x.symm)
    uq_eq = uq_eq.rw(def_eq_a.symm)
    uqy_nn = in_domain_elim(y_in_domain)
    uqy_nn = uqy_nn.rw(def_apply_inverse)
    ex_uq_y = unique_nn_to_exists_uq(uqy_nn)
    fb_y, _, def_eq_b = get_example(ex_uq_y, 'B', with_def_eq = True)
    uq_eq = uq_eq.rw(def_eq_b.symm)
    g.rw(fb_y.symm)
    g.rw(uq_eq).app(axiom.eq_refl)
inverse_injective = g.last_proven

with g.goal("f is_Fun => g is_Fun => forall(x : x is_sane => f[x] = g[x]) => f = g"):
    f_fun, g_fun, x = g.intros()
    g.rw(axiom.fun_repr(f_fun).symm)
    g.rw(axiom.fun_repr(g_fun).symm)
    g.app(axiom.fun_ext).introv()
    x_sane = g.cases("X is_sane")
    g.exact(forall_elim(x)(x_sane))
    x_nsane = g.get_last_output()
    g.rw(axiom.fun_repr(f_fun).symm)
    g.rw(axiom.fun_repr(g_fun).symm)
    g.rw(axiom.def_apply_fun, req_false(x_nsane), repeat = True)
    g.app(axiom.eq_refl)
fun_eq_intro = g.last_proven

with g.goal("f is_injective => inverse(inverse(f)) = f"):
    f_inj = g.intro()
    f_fun = injective_is_fun(f_inj)
    g.app(fun_eq_intro)
    g.exact(inverse_is_fun(inverse_is_fun(f_fun)))
    g.exact(f_fun)
    x_sane = g.introv().intro()
    with g.goal("domain(inverse(inverse(f))) = domain(f)"):
        g.rw(domain_inverse(inverse_injective(f_fun)))
        g.exact(image_inverse(f_inj))
    dii_is_d = g.last_proven
    x_in_d = g.cases("X in domain(f)")
    with g.subgoal():
        g.rw(def_apply_inverse)
        uqnn = in_domain_elim(x_in_d.rw(dii_is_d.symm)).rw(def_apply_inverse)
        eq_uq = unique_nn_to_exists_uq(uqnn)
        ify_x,uq,def_eq = get_example(eq_uq, 'Y', with_def_eq = True)
        g.rw(def_eq.symm).symm()
        g.app(uq).app(inverse_left).rw(domain_inverse(f_inj))
        g.exact(in_image_intro(in_domain_elim(x_in_d), axiom.eq_refl))
    x_nin_d = g.get_last_output()
    with g.subgoal():
        g.rw(nimpl_symm(in_domain_intro, x_nin_d))
        x_nin_dii = x_nin_d.rw(dii_is_d.symm)
        g.exact(nimpl_symm(in_domain_intro, x_nin_dii))
inverse_inverse = g.last_proven
print("Double inverse:")
print(inverse_inverse)

with g.goal("X != null => X = inverse(f) [Y] => f[X] = Y"):
    xnn, x_ify = g.intros()
    g.rw(x_ify)
    g.exact(inverse_right(in_domain_intro(xnn.rw(x_ify))))
eq_inverse_elim = g.last_proven

with g.goal("f is_injective => f[X] != null => f[X] = f[Y] => X = Y"):
    f_inj, fxnn, fxfy = g.intros()
    f_fun, x = f_inj.rw(co._is_injective).split()
    xd = in_domain_intro(fxnn)
    yd = in_domain_intro(fxnn.rw(fxfy))
    x = to_bool1_idemp(forall_elim_full(x, X = 'X')(xd))
    x = to_bool1_idemp(forall_elim_full(x, X = 'Y')(yd))
    g.exact(x(fxfy))
injective_cancel_nn = g.last_proven    

with g.goal("""
  f is_injective => g is_injective =>
  image(f) <:= domain(g) => image(g) <:= domain(f) =>
  exists(bij :
    bij is_injective && domain(bij) = domain(f) && image(bij) = domain(g)
  )
"""):
    cantor_bernstein_statement = g.current_goal.term
    f_inj, g_inj, f_into, g_into = g.intros()
    f_fun = injective_is_fun(f_inj)
    g_fun = injective_is_fun(g_inj)

    s_def = local_def("""S = set(x :
       forall(Sc :
         domain(f) \ image(g) <:= Sc =>
         forall(y : y in Sc => g[f[y]] in Sc) =>
         x in Sc
    ))
    """)
    with g.goal("X in S => X in domain(f)"):
        xs = g.intro()
        x_sane, x = axiom.def_in_set(xs.rw(s_def)).split()
        x = forall_elim(x, X = "domain(f)")
        x = x(setdiff_is_subset(domain_is_set(f_fun), image_is_set(g_fun)))
        g.app(x)
        x = g.introv('X2').intro()
        g.app(subset_to_in_impl(g_into)).app(in_image_intro(0, axiom.eq_refl))
        g.app(in_domain_elim).app(subset_to_in_impl(f_into))
        g.exact(in_image_intro(in_domain_elim(x), axiom.eq_refl))
    s_to_df = g.last_proven.freeze(('S', 'f'))
    with g.goal("X in S => g[f[X]] in S"):
        xs = g.intro()
        x_sane, x = axiom.def_in_set(xs.rw(s_def)).split()
        g.rw(s_def).rw(def_in_set_eq)
        g.cases()
        g.app(value_is_sane).app(in_domain_elim)
        g.app(subset_to_in_impl(f_into)).app(in_image_intro).app(in_domain_elim)
        g.exact(s_to_df(xs)).app(axiom.eq_refl)
        g.introv('Sc')
        x = forall_elim(x, X = 'Sc')
        st,cl =  g.intros()
        x = x(st,cl)
        g.exact(forall_elim(cl, X = 'X')(x))
    s_closed = g.last_proven.freeze(('S', 'f', 'g'))

    bij_def = local_def("bij = fun(x : if x in S; f[x] else inverse(g)[x])")
    with g.goal("bij is_Fun"):
        g.rw(bij_def)
        g.app(axiom.fun_is_fun)
    bij_fun = g.last_proven
    g.app(exists_intro(X = "bij"))
    g.cases()
    with g.subgoal("domain(bij) = domain(f) && image(bij) = domain(g)"):
        g.cases()

        with g.subgoal("domain(bij) = domain(f)"):
            g.app(set_eq_intro)
            g.exact(domain_is_set(bij_fun))
            g.exact(domain_is_set(f_fun))
            g.introv('X').cases()
            with g.subgoal("X in domain(bij) => X in domain(f)"):
                x = g.intro()
                x_sane = element_is_sane(x)
                x = in_domain_elim(x.rw(bij_def))
                x = x.rw(def_apply_fun_nn(x))
                xs = g.cases("X in S")
                g.app(in_domain_intro)
                g.exact(x.rw(axiom.if_true(xs)))
                xns = g.get_last_output()
                x = x.rw(axiom.if_false(xns))
                x = in_domain_intro(x)
                x = x.rw(domain_inverse(g_inj))
                g.exact(subset_to_in_impl(g_into, x))
            with g.subgoal("X in domain(f) => X in domain(bij)"):
                x_in_df = g.intro()
                x_sane = element_is_sane(x_in_df)
                fx_sane = value_is_sane(in_domain_elim(x_in_df))
                g.app(in_domain_intro)
                g.rw(bij_def).rw(axiom.def_apply_fun).rw(req_true(x_sane))
                xs = g.cases("X in S")
                g.rw(axiom.if_true(xs)).rw(co.req_sane).rw(req_true(fx_sane))
                g.exact(sane_to_not_null(fx_sane))
                xns = g.get_last_output()
                g.rw(axiom.if_false(xns))
                with g.goal("X !in domain(f) \ image(g)"):
                    x_in_sd = g.by_contradiction().intro()
                    g.app(contr(xns))
                    g.rw(s_def).rw(def_in_set_eq)
                    g.cases().exact(x_sane)
                    sc_sub,_ = g.introv('Sc').intros()
                    g.exact(subset_to_in_impl(sc_sub, x_in_sd))
                x = avoiding_setdiff(image_is_set(g_fun), x_in_df, g.last_proven)
                x = x.rw(domain_inverse(g_inj).symm)
                x = in_domain_elim(x)
                igx_sane = value_is_sane(x)
                g.rw(co.req_sane).rw(req_true(igx_sane))
                g.exact(sane_to_not_null(igx_sane))
        bij_domain = g.last_proven.freeze()
        
        with g.subgoal("image(bij) = domain(g)"):
            g.app(set_eq_intro)
            g.exact(image_is_set(bij_fun))
            g.exact(domain_is_set(g_fun))
            g.introv('Y').cases()
            with g.subgoal("Y in image(bij) => Y in domain(g)"):
                y = g.intro()
                y_sane = element_is_sane(y)
                ynn = sane_to_not_null(y_sane)
                y = in_image_elim(y)
                y_bx = get_example(y, 'X')
                y_bx = y_bx.rw(bij_def)
                y_bx = y_bx.rw(def_apply_fun_nn(ynn.rw(y_bx)))
                xs = g.cases("X in S")
                y_bx1 = y_bx.rw(axiom.if_true(xs))
                g.app(subset_to_in_impl(f_into))
                g.app(in_image_intro).exact(ynn).exact(y_bx1)
                xns = g.get_last_output()
                y_bx2 = y_bx.rw(axiom.if_false(xns))
                y = in_image_intro(ynn, y_bx2)
                y = y.rw(image_inverse(g_inj))
                g.exact(y)
            with g.subgoal("Y in domain(g) => Y in image(bij)"):
                y_in_dg = g.intro()
                y_sane = element_is_sane(y_in_dg)
                ynn = sane_to_not_null(y_sane)
                g.rw(bij_def)
                gys = g.cases("g[Y] in S")

                with g.goal("!forall(x : x in S => f[x] != Y)"):
                    y_first = g.by_contradiction().intro()
                    gy_sane, gys = gys.rw(s_def).rw(def_in_set_eq).split()
                    s2_def = local_def("S2 = set(x : x in S && x != g[Y])")
                    with g.goal("S2 is_Set"):
                        g.rw(s2_def).app(axiom.set_is_set)
                    s2_is_set = g.last_proven()
                    gys = forall_elim(gys, X = "S2")
                    with g.goal("g[Y] !in S2"):
                        x = g.by_contradiction().intro()
                        x = x.rw(s2_def).rw(def_in_set_eq).split()[1]
                        x = x.split()[1]
                        g.exact(contr(x, axiom.eq_refl))
                    g.app(contr(g.last_proven))
                    g.app(gys)
                    with g.subgoal("domain(f) \ image(g) <:= S2"):
                        g.rw(co._subset_eq)
                        g.cases().exact(setdiff_is_set(
                            domain_is_set(f_fun), image_is_set(g_fun)
                        ))
                        g.cases().exact(s2_is_set)
                        x_in_sd = g.introv('X').intro()
                        x_sane = element_is_sane(x_in_sd)
                        xnn = sane_to_not_null(x_sane)
                        x_gy = g.cases("X = g[Y]")
                        _,xnig = in_setdiff_elim(x_in_sd).split()
                        xnig = xnig.rw(x_gy)
                        g.app(axiom.false).app(contr(xnig))
                        g.exact(in_image_intro(xnn.rw(x_gy), axiom.eq_refl))
                        x_ngy = g.get_last_output()
                        g.rw(s2_def).rw(def_in_set_eq)
                        g.cases().exact(x_sane)
                        g.cases().rw(s_def).rw(def_in_set_eq)
                        g.cases().exact(x_sane)
                        g.introv('Sc')
                        sc_sup, _ = g.intros()
                        g.exact(subset_to_in_impl(sc_sup, x_in_sd))
                        g.exact(x_ngy)
                    with g.subgoal("forall(x : x in S2 => g[f[x]] in S2)"):
                        xs2 = g.introv('X').intro()
                        x_sane, xs2 = axiom.def_in_set(xs2.rw(s2_def)).split()
                        xs,_ = xs2.split()
                        xdf = s_to_df(xs)
                        gfxs = s_closed(xs)
                        gfx_sane = element_is_sane(gfxs)
                        g.rw(s2_def).rw(def_in_set_eq)
                        g.cases().exact(gfx_sane)
                        g.cases().exact(gfxs)
                        x = g.by_contradiction().intro()
                        x = injective_cancel_nn(g_inj, sane_to_not_null(gfx_sane), x)
                        g.exact(contr(forall_elim(y_first, X = 'X')(xs), x))
                with g.goal("exists(x : x in S && f[x] = Y)"):
                    x = dneg_elim(g.last_proven.rw(co.forall))
                    x = get_example(x, 'X').rw(to_bool1_idemp)
                    xs, fx_y = x.split()
                    g.app(exists_intro(X = 'X'))
                    g.cases().exact(xs)
                    g.exact(dneg_elim(fx_y))
                xs, fx_y = get_example(g.last_proven).split()
                g.app(in_image_intro(ynn)).rw(axiom.def_apply_fun)
                g.rw(req_true(element_is_sane(xs)))
                g.rw(axiom.if_true(xs))
                g.rw(fx_y).rw(co.req_sane)
                g.rw(req_true(y_sane)).app(axiom.eq_refl)
                gyns = g.get_last_output()
                with g.subgoal():
                    g.app(in_image_intro(ynn, X = "g[Y]"))
                    g.rw(axiom.def_apply_fun)
                    gynn = in_domain_elim(y_in_dg)
                    gy_sane = value_is_sane(gynn)
                    g.rw(req_true(gy_sane))
                    g.rw(axiom.if_false(gyns))
                    g.app(eq_req_sane_intro(y_sane))
                    g.symm()
                    g.app(inverse_left).rw(domain_inverse(g_inj))
                    g.app(in_image_intro(gynn, axiom.eq_refl))

    with g.subgoal("bij is_injective"):
        g.rw(co._is_injective).cases().exact(bij_fun)
        x1db = g.introv('X1', full = True).app(to_bool1_req_intro).intro()
        g.app(to_bool1_intro)
        x2db = g.introv('X2', full = True).app(to_bool1_req_intro).intro()
        bx1_bx2 = g.app(to_bool1_intro).intro()
        x1df = x1db.rw(bij_domain)
        x2df = x2db.rw(bij_domain)
        fx1_nn = in_domain_elim(x1df)
        fx2_nn = in_domain_elim(x2df)
        x1_sane = element_is_sane(x1db)
        x2_sane = element_is_sane(x2db)
        bx1_nn = in_domain_elim(x1db)
        bx1_nn = bx1_nn.rw(bij_def, axiom.def_apply_fun)
        bx1_nn = req_nn_nn(bx1_nn.rw(bij_def, axiom.def_apply_fun))
        bx1_sane = req_nn_to_C(bx1_nn.rw(co.req_sane))
        bx2_nn = in_domain_elim(x2db)
        bx2_nn = bx2_nn.rw(bij_def, axiom.def_apply_fun)
        bx2_nn = req_nn_nn(bx2_nn.rw(bij_def, axiom.def_apply_fun))
        bx2_sane = req_nn_to_C(bx2_nn.rw(co.req_sane))
        bx1_bx2 = bx1_bx2.rw(bij_def, axiom.def_apply_fun, repeat = True)
        bx1_bx2 = bx1_bx2.rw(req_true(x1_sane)).rw(req_true(x2_sane))
        bx1_bx2 = bx1_bx2.rw(co.req_sane, repeat = True)
        bx1_bx2 = bx1_bx2.rw(req_true(bx1_sane)).rw(req_true(bx2_sane))
        x1s = g.cases("X1 in S")
        x2s = g.cases("X2 in S")
        # X1 in S, X2 in S
        x = bx1_bx2.rw(axiom.if_true(x1s)).rw(axiom.if_true(x2s))
        g.app(injective_cancel_nn(f_inj, 0, x))
        g.exact(fx1_nn)
        # X1 in S, X2 !in S
        x2ns = g.get_last_output()
        x = bx1_bx2.rw(axiom.if_true(x1s)).rw(axiom.if_false(x2ns))
        gfx1_x2 = eq_inverse_elim(fx1_nn, x)
        g.app(axiom.false)
        g.app(contr(x2ns, s_closed(x1s).rw(gfx1_x2)))
        # X1 !in S, X2 in S
        x1ns = g.get_last_output()
        x2s = g.cases("X2 in S")
        x = bx1_bx2.rw(axiom.if_false(x1ns)).rw(axiom.if_true(x2s))
        gfx2_x1 = eq_inverse_elim(fx2_nn, x.symm)
        g.app(axiom.false)
        g.app(contr(x1ns, s_closed(x2s).rw(gfx2_x1)))
        # X1 !in S, X2 !in S
        x2ns = g.get_last_output()
        x = bx1_bx2.rw(axiom.if_false(x1ns)).rw(axiom.if_false(x2ns))
        igx1_nn = sane_to_not_null(bx1_sane.rw(axiom.if_false(x1ns)))
        x = eq_inverse_elim(igx1_nn, x)
        x = x.rw(inverse_right(in_domain_intro(igx1_nn)))
        g.exact(x)

cantor_bernstein = g.last_proven
cantor_bernstein = cantor_bernstein.alpha_equiv_exchange(
    cantor_bernstein_statement
)
print("Cantor Bernstein:")
print(cantor_bernstein)
