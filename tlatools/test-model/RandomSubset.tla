--------------------------- MODULE RandomSubset ---------------------------
EXTENDS Integers

VARIABLE x, y, z

Init == /\ x \in 1..100000000
        /\ y \in 100000000..100000010
        /\ z = TRUE

Next == /\ UNCHANGED <<x, y>>
        /\ z' = FALSE
        

Spec == Init /\ [][Next]_<<x,y,z>>

Inv == z = TRUE
=============================================================================
