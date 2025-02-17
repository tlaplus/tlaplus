This error is caused by providing an expression as an argument to an operator
when a higher-order operator is required.
---- MODULE E2024_Test ----
op(F(_)) == 0
op2 == op({})
====

