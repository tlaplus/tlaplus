Nested module declarations cannot occur in between the declaration of a
recursive operator and its definition.
---- MODULE E4294_Module_Test ----
RECURSIVE op
---- MODULE Inner ----
====
op == 0
====

