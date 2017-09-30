------------------------------ MODULE AssertExpressionStack ------------------------------
EXTENDS Naturals, TLC

VARIABLES x

Spec == x = 0 /\ [][x'=1/\Assert(x=0, "Fails after initial state")]_x
=============================================================================
