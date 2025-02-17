If an operator takes a higher-order operator as a parameter, any operator
passed to it as an argument must have the correct arity.
---- MODULE E4271_1_Required_2_Provided_Test ----
op(F(_)) == 0
op2(x, y) == 0
op3 == op(op2)
====

