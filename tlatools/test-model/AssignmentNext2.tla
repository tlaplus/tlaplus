--------------------------- MODULE AssignmentNext2 ---------------------------
EXTENDS Integers
VARIABLE s

Next(var) == \E val \in 0..1: (var = val /\ var > 0)

Spec == s = "" /\ [][Next(s')]_s

=============================================================================
