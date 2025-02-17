If a symbol is already defined, its name cannot be re-used as an operator
parameter name.
---- MODULE E2006_OpParameter_Test ----
VARIABLE x
op(x) == 0
====

