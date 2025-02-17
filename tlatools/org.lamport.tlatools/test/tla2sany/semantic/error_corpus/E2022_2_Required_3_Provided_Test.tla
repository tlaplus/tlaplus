Simple error. Calling an operator with the wrong number of arguments.
---- MODULE E2022_2_Required_3_Provided_Test ----
op(x, y) == 0
op2 == op(0, 0, 0)
====

