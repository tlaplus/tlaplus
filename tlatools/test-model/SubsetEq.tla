------------------------------ MODULE SubsetEq ------------------------------
EXTENDS Integers, FiniteSets

VARIABLE b

Init == b = TRUE

Next == b' = /\ (SUBSET (1..23) \subseteq SUBSET (1..42))
             /\ ~(SUBSET (1..42) \subseteq SUBSET (1..23))
             /\ ~(SUBSET (1..42) \subseteq SUBSET (2..42))
             /\ (SUBSET (2..42) \subseteq SUBSET (1..42))
             /\ (SUBSET {1,2,3} \subseteq SUBSET {1,2,3,4})
             /\ (SUBSET {} \subseteq SUBSET {})
             /\ (SUBSET {} \subseteq SUBSET {1})
             /\ ~(SUBSET {1} \subseteq SUBSET {})
             /\ (SUBSET {1} \subseteq SUBSET Int)
             /\ (SUBSET {1} \subseteq SUBSET Nat)

Spec == Init /\ [][Next]_<<b>>

Inv == b = TRUE /\ b \in BOOLEAN
=============================================================================
