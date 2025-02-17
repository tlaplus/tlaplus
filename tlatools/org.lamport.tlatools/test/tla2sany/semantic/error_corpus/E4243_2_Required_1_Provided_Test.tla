When importing a module with INSTANCE, a substitute for a constant operator
must have the correct arity.
---- MODULE E4243_2_Required_1_Provided_Test ----
---- MODULE Inner ----
CONSTANT F(_, _)
====
op(x) == 0
INSTANCE Inner WITH F <- op
====

