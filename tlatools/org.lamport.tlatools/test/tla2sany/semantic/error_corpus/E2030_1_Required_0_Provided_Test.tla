When importing a module with INSTANCE, a substitute for a constant operator
must have the correct arity.
---- MODULE E2030_1_Required_0_Provided_Test ----
---- MODULE Inner ----
CONSTANT F(_)
====
op == 0
INSTANCE Inner WITH F <- op
====

