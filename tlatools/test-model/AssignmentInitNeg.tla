--------------------------- MODULE AssignmentInitNeg ---------------------------
EXTENDS Integers
VARIABLE s

Init(var) == \E val \in 0..1: (var = val /\ var < 1)

Spec == Init(s) /\ [][UNCHANGED s]_s

Inv == (s < 1)
=============================================================================
