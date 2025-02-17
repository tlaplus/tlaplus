A recursive operator's definition must have the same arity as its declaration
following the RECURSIVE keyword.
---- MODULE E2044_Function_Test ----
RECURSIVE F(_)
F[x \in {}] == 0
====

