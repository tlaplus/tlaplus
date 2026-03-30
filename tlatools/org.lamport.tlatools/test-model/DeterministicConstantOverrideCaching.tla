---------------- MODULE DeterministicConstantOverrideCaching ----------------
EXTENDS TLC, FiniteSets, Naturals

CONSTANT C

VARIABLE x

D == Print("CONST_EVAL", 1..3)

Init == x = 0

Next == /\ x < Cardinality(C)
        /\ x' = x + 1

Inv == x <= Cardinality(C)

=============================================================================
