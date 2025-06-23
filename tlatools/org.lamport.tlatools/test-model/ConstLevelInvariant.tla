---- MODULE ConstLevelInvariant ----
EXTENDS Naturals

CONSTANT C

VARIABLE b

Init ==
    b = FALSE

Next ==
    b' = TRUE

Spec ==
	Init /\ [][Next]_b

ConstLevelInvariant ==
    C \subseteq Nat

=============================================================================
---- CONFIG ConstLevelInvariant ----
SPECIFICATION Spec
CONSTANT C = {1, 2, 3}
INVARIANT ConstLevelInvariant
====