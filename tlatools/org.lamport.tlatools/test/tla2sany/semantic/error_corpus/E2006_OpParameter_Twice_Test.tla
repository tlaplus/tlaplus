A symbol cannot be used twice as a parameter to an operator definition.
---- MODULE E2006_OpParameter_Twice_Test ----
op(x, x) == 0
====

