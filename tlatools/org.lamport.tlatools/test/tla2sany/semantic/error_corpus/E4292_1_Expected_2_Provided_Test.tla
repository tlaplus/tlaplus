A recursive operator's definition must have the same arity as its declaration
following the RECURSIVE keyword.
---- MODULE E4292_1_Expected_2_Provided_Test ----
RECURSIVE op(_)
op(x, y) == 0
====

