# PyLogic -- Pythonic Interactive Theorem Prover

PyLogic is a logical system for formally stating and proving theorems (a bit similar like Isabelle / Coq / Lean...). Axioms / definitions can be parsed from external files, the proving part is done as a pure python code. It is already possible to play with it, and prove basic facts about sets / functions. As a challenge, I proved the Cantor-Bernstein theorem at the end of the file [proving_test.py](proving_test.py). On the other hand, the code is rather preliminary, not recommended for large theory building.

## Quick start

For trying it out, first run
```
python proving_test.py
```
to see some of the theorems I have proven in that file. As a further step, open and play with `proving_test.py` by yourself, for example go to the middle of the file and:
* insert `print(<something>)` and `exit()` on the next line where `<something>` is an object occuring at that point. You can print the terms / theorems used at that point
* terminate one of the blocks `with g.goal():` prematurely, e.g. by commenting out the end, or putting `if False:` there. You will get an exception of unfinished proof, and the program will print the remaining goals.

(sorry for occasional not very comprehensible errors)

## Logical foundations

### Language & rules

At its core, PyLogic uses second / third order logic (I don't know exactly how orders are counted). In particular:
* Every bound variable represents a first-order logic object.
* Free variables (some could call them meta-variables) can take arguments, so they could be considered 2nd order. Note that this is mostly to deal with binders, most of free variables are without arguments, and therefore also first-order.
* Constants can be up to third order -- that is a fancy way of saying that they can introduce bound variables at their arguments. The number of bound variables introduced per argument is syntactially fixed for each constant. Note however that almost all such constants introducing bound variables (`forall(x : PRED(x))`, `exists(x : PRED(x))`, `example(x : PRED(x))`, `fun(x : BODY(x))`, `set(x : PRED(x))`, ...) have a single argument introducing a single bound variable.

There are two basic logical rules:
* Modus ponens: if `<TERM1> => <TERM2>` is a theorem, and `<TERM1>` is a theorem, then `<TERM2>` is a theorem.
* Specialization: for any theorem `THM`, one can obtain another theorem by assigning terms (possibly again containing varaibles) to its free variables. A free variable however cannot be substituted with a bound variable (because such assignment wouldn't be context-free). So `fun(x : A)` can be specialized into `fun(x : true)` but not into `fun(x : x)``

The core logic also allows creating new definitions:
* If `<term>` is a term containing no free variables except (distinct) `v1`, ..., `vn`, then one can introduce a new constant `c`, and add a new theorem `c(v1,...,vn) = <term>`. If some of the variables `vi` are parametrized (second order), the i-th argument of `c` introduces as many bound variables as the arity of `vi`.

### Axiomatic foundations

Currently used axioms can be found in files [axioms_logic](axioms_logic), [axioms_set](axioms_set), and [axioms_fun](axioms_fun). Other files which are not a python code were just design experimentats, and are not usable by the current code. You can read the axioms on your own, here I state a few ideas behind them.

* classical logic -- all logical connectives / predicates are outputing a boolean value (true or false). Logical connectives moreover depend only on the bool-converted values of their arguments
* almost-decidability -- I am trying not to leave much undecidable statements for "stupid reasons" of insufficient definitions. Therefore, incorrect application of a function leads to a `null` value (except predicates / connectives, they return always boolean).
* no need for minimality -- I intend this for playing with logic, not for theory building from minimal foundations. For this reason, I distinguish the basic "types" of booleans / sets / functions / null contrary to purely set-theory based systems where everything is a set. Eventually, I also plan to add the type of numbers.
* `is_sane` predicate (soft type?) -- sets and functions can be defined arbitrarily. However, to avoid Russel-like paradoxes, they are forced to act only of "sane" (small) objects -- the objects that would correspond to "sets and not classes" in standard set theory. Note that `null` is not considered `sane`, so the domain of a function is well defined as the set on which the function returns non-`null` values.

### Labelled assumptions

Although this feature is just a convenience, it is implemented already in the logical core -- a theorem in the core is not only a term but a term together with a dictionary of assumptions (`dict[AssumptionLabel, Term]`). Such assumptions can be converted into the standard assumptions (prepending `A => `), and vice versa. When modus ponens is applied, it is applied only on the main terms, and the assumptions of both statements get merged (if there is a conflict in an equally labelled assumption, the logical core raises an exception).

## Above core

I am planning to change this quite significantly, so just a few words. For proving convenience, I am mostly not using CoreTheorem but Theorem. It contains just a very little data above CoreTheorem, in particular which variables should be considered "frozen" (fixed), and how to handle some specific labels. Functionality-wise, it performs automatic unification, and offers coder friendly Python interface (various methods, `__call__` can be used for modus_ponens / variable substitutions...)

For matching a goal, there is a goal context creating a tree-plan of constructing the desired term. Every subgoal is just the simple term (context is not checked but possible to lookup). This tree is extended by calling tactics as methods of `env.goal_env`. An assumption returned from `g.intros()` is just a labelled implication reflexivity which is eventually (when the final proof is constructed) turned into a positional assumption.
