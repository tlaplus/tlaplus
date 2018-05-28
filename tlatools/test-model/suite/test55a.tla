------------------------------- MODULE test55a ------------------------------
EXTENDS Naturals
VARIABLES x, y

F == ENABLED (x'=0 /\ y'=1)
G == ENABLED ((x # y) /\ (x'=0) /\ (y'=1))

Init == (x = 0) /\ (y = 0)
Next == /\ x' = 1 - x
        /\ y' = y

SafeSpec == Init /\ [][Next]_<<x,y>>
LiveSpec == SafeSpec /\ WF_<<x,y>>(Next)
=============================================================================
