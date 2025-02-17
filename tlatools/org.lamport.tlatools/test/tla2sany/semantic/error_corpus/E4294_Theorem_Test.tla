Theorems cannot occur in between the declaration of a recursive operator and
its definition.
---- MODULE E4294_Theorem_Test ----
RECURSIVE op
THEOREM TRUE
op == 0
====

