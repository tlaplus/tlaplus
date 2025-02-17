New variable declarations cannot occur in between the declaration of a
recursive operator and its definition.
---- MODULE E4294_Variable_Test ----
RECURSIVE op
VARIABLE v
op == 0
====

