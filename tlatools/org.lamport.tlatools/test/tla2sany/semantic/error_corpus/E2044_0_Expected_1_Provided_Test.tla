A recursive operator's definition must have the same arity as its declaration
following the RECURSIVE keyword.
---- MODULE E2044_0_Expected_1_Provided_Test ----
RECURSIVE op
op(x) == x
====

