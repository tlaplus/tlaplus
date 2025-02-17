When importing a module with INSTANCE, a substitute for a constant operator
must have the correct arity.
---- MODULE E2030_1_Required_2_Provided_Test ----
---- MODULE Inner ----
CONSTANT F(_)
====
op(x, y) == 0
INSTANCE Inner WITH F <- op
====

