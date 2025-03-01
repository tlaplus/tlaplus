Parameterized labels must be given the correct number of arguments.
---- MODULE E2047_Test ----
op == \A x \in {} : lbl(x) :: 0
op2 == op!lbl(0, 0)
====

