This error is caused by providing a LAMBDA operator of incorrect arity as an
argument to an operator accepting a higher-level operator parameter.
---- MODULE E2025_2_Required_3_Provided_Test ----
op(F(_, _)) == 0
op2 == op(LAMBDA x, y, z : 0)
====

