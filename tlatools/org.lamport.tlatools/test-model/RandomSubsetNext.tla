------------------------- MODULE RandomSubsetNext -------------------------
EXTENDS Integers, Randomization

VARIABLE x, y

Init == /\ x \in RandomSubset(10, 1..1000)
        /\ y = 0

Next == /\ x'\in RandomSubset(10, 1..1000)
        /\ y' = y + 1
        
Spec == Init /\ [][Next]_<<x,y>>

Inv == y < 10
=============================================================================
