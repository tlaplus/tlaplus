Can only substitute constants or variables, not operators.
---- MODULE E4242_Illegal_Test ----
---- MODULE Inner ----
c == TRUE
====
INSTANCE Inner WITH c <- 0
====

