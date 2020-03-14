--------------------------- MODULE AssignmentNext ---------------------------
EXTENDS Integers
VARIABLE s

Next(var) == \E val \in 0..1: (var' = val /\ var' > 0)

Spec == s = 23 /\ [][Next(s)]_s

Inv == s # 0
=============================================================================
