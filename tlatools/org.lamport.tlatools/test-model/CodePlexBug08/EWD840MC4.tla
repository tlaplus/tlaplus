---- MODULE EWD840MC4 ----
EXTENDS EWD840, TLC

const_123 == 4

neg_AllNodesTerminateIfNoMessages == ~AllNodesTerminateIfNoMessages

Tautology == (vars = vars) ~> (vars = vars)
===================