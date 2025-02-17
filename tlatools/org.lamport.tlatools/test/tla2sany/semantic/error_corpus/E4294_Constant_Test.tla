Constant declarations cannot occur in between the declaration of a recursive
operator and its definition.
---- MODULE E4294_Constant_Test ----
RECURSIVE op
CONSTANT c
op == 0
====

