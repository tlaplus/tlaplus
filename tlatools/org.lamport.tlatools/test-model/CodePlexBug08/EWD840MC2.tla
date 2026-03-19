---- MODULE EWD840MC2 ----
EXTENDS EWD840, TLC

const_123 == 4

Tautology == (vars = vars) ~> (vars = vars)
===================