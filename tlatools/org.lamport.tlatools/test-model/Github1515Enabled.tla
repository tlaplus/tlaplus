------------------------- MODULE Github1515Enabled -------------------------
\* https://github.com/tlaplus/tlaplus/issues/1515
EXTENDS Naturals

VARIABLE pc

F == [[i \in Nat |-> FALSE] EXCEPT ![2] = TRUE]

Init == pc = 0
Next == UNCHANGED pc

Inv == ~( ENABLED ( F[2] /\ pc' = 1 ) )
=============================================================================
