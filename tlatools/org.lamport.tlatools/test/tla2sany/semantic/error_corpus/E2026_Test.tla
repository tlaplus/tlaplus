This error is caused by providing a LAMBDA as an argument to an operator when
an expression is required.
---- MODULE E2026_Test ----
op(x) == 0
op2 == op(LAMBDA x : 0)
====

