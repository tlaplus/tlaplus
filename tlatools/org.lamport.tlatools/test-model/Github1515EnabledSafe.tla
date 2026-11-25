---- MODULE Github1515EnabledSafe ----
EXTENDS Naturals

CONSTANT Override
VARIABLE pc

F == [[i \in Nat |-> FALSE] EXCEPT ![2] = Override]

Init == pc = 0
Next == UNCHANGED pc
Spec == Init /\ [][Next]_pc

BadInv == ~(ENABLED (F[2] /\ pc' = 1))
====
