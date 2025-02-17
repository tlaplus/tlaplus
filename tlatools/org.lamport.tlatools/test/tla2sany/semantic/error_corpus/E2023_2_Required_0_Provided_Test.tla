If an operator takes a higher-order operator as a parameter, any operator
passed to it as an argument must have the correct arity.
---- MODULE E2023_2_Required_0_Provided_Test ----
op(F(_, _)) == 0
op2 == 0
op3 == op(op2)
====

