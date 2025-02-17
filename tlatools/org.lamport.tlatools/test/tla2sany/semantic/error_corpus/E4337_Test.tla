Parameterized labels must be given the correct number of arguments.
---- MODULE E4337_Test ----
op == \A x \in {} : lbl(x) :: TRUE
op2 == op!lbl(0, 0)
====

