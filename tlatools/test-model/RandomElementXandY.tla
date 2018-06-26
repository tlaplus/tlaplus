--------------------------- MODULE RandomElementXandY ---------------------------
EXTENDS Integers, TLC

VARIABLE x, y

Init == /\ x = 0
        /\ y = 0

Next == /\ x' = RandomElement(0..1)
        /\ y' = RandomElement(0..1)
        

Spec == Init /\ [][Next]_<<x,y>>

Inv == x = y
=============================================================================
