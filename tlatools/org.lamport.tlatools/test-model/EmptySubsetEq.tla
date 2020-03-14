--------------------------- MODULE EmptySubsetEq --------------------------
EXTENDS Integers, FiniteSets

VARIABLE b

Init == b = TRUE

Next == b' = /\ (SUBSET (1..3)) \subseteq (1..4)

Spec == Init /\ [][Next]_<<b>>

Inv == b = TRUE
=============================================================================
