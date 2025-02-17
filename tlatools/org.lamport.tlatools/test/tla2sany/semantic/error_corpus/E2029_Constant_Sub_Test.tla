When importing a non-constant module as an INSTANCE and performing
substitutions, each constant & variable must be substituted by a symbol of
the same level. If the imported module is fully constant the levels of the
substitutions do not matter.
---- MODULE E2029_Constant_Sub_Test ----
---- MODULE Inner ----
CONSTANT c
VARIABLE v1
====
VARIABLE v2
INSTANCE Inner WITH c <- v2, v1 <- v2
====

