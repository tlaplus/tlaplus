It is an error to provide multiple substitutions for the same symbol when
importing a module using INSTANCE.
---- MODULE E4241_Test ----
---- MODULE Inner ----
CONSTANT c
====
INSTANCE Inner WITH c <- 0, c <- 0
====
