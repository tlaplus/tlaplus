Use/Hide blocks cannot occur in between the declaration of a recursive
operator and its definition.
---- MODULE E4294_Use_or_Hide_Test ----
RECURSIVE op
USE op
op == 0
====

