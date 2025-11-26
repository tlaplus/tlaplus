# When to use ASSUME/ASSUMPTION and when to use INVARIANT/INVARIANTS with TLC?

The `ASSUME` (or `ASSUMPTION`) keyword in TLA+ is used to introduce constant-level (level 0) formulas—facts that must hold about the constants and fixed structures of a specification. These constraints are evaluated before TLC begins exploring behaviors and are not interpreted as invariants or properties of system states.
A constant-level (level 0) formula contains no state variables, no primed variables, and no temporal operators. It expresses purely mathematical truths about constants, sets, or other static objects. Such formulas might assert, for example, that a constant N is a natural number or that a given set S is nonempty.

In contrast, `INVARIANT` (or `INVARIANTS`) entries in a TLC configuration file refer to state-level (level 1) formulas—predicates about the values of state variables in a single state. Although these predicates must be true in every reachable state, they are not temporal formulas themselves; rather, TLC interprets them as safety checks. An invariant might state that a counter never becomes negative or that two variables always remain equal.

```tla
---- MODULE Example ----
CONSTANT N

ASSUME N \subseteq (Nat \ {0})

VARIABLE x

...

Inv == x \in N
====
```

```cfg
...
CONSTANT N = {1, 2, 3}
INVARIANT Inv
```

Note that `ASSUME` is a keyword in TLA+, whereas `INVARIANT` is a keyword used in TLC configuration files. Furthermore, assumptions introduced with `ASSUME` are automatically checked by TLC, while a state predicate such as `Inv` is checked only if the configuration file explicitly instructs TLC to do so by including it under an `INVARIANT` entry.