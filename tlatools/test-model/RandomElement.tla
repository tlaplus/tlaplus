--------------------------- MODULE RandomElement ---------------------------
EXTENDS Integers, TLC

VARIABLE x, y

Init == /\ x = RandomElement(1..1000)
        /\ y = 0

Next == /\ \/ x' = RandomElement(1..1000)
           \/ x' = x
        /\ y' = y + 1
        

Spec == Init /\ [][Next]_<<x,y>>

Inv == y < 10
=============================================================================
