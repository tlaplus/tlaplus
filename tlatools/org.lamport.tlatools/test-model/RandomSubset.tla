--------------------------- MODULE RandomSubset ---------------------------
EXTENDS Integers, Randomization

VARIABLE x, y, z

Init == /\ x \in RandomSubset(1001, 1..100000000)
        /\ y \in RandomSubset(2, 100000000..100000010)
        /\ z = TRUE

Next == /\ UNCHANGED <<x, y>>
        /\ z' = FALSE
        

Spec == Init /\ [][Next]_<<x,y,z>>

Inv == z = TRUE
=============================================================================
