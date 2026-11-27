-------------------------- MODULE Github1515Nested --------------------------
\* https://github.com/tlaplus/tlaplus/issues/1515
EXTENDS Naturals

VARIABLE pc

F == [[i \in UNION {1..2} |-> [j \in UNION {1..2} |-> FALSE]] EXCEPT ![2][2] = TRUE]

Init == pc = 0
Next == pc = 0 /\ F[2][2] /\ pc' = 1
Inv == pc # 1
=============================================================================
