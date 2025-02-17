This error is caused by providing an expression as an argument to an operator
when a higher-order operator is required.
---- MODULE E4270_Test ----
op(F(_)) == 0
op2 == op({})
====

