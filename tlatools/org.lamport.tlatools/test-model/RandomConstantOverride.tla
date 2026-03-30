---------------------- MODULE RandomConstantOverride ------------------------
EXTENDS TLC, Naturals

CONSTANT C

VARIABLE x

R == Print("RAND_EVAL", RandomElement(1..3))

Init == x = 0

Next == /\ x < 3
        /\ x' = x + C

Inv == x >= 0

=============================================================================
