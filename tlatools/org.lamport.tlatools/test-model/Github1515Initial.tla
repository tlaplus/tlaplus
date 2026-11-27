------------------------- MODULE Github1515Initial -------------------------
\* https://github.com/tlaplus/tlaplus/issues/1515
VARIABLE pc

F == [[i \in SUBSET { 1, 2 } |-> FALSE] EXCEPT ![{ 1 }] = TRUE]

Init == ( F[{ 1 }] /\ pc = 0 ) \/ ( pc = 1 )
A == pc = 0 /\ pc' = 2
B == pc = 1 /\ UNCHANGED pc
Next == A \/ B
Inv == pc # 2
=============================================================================
