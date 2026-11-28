---- MODULE Github1515InitialSafe ----
EXTENDS Naturals

CONSTANT Override
VARIABLE pc

F == [[s \in SUBSET {1, 2} |-> FALSE] EXCEPT ![{1}] = Override]

Init == (F[{1}] /\ pc = 0) \/ pc = 1

Bad == pc = 0 /\ pc' = 2
Done == pc = 1 /\ UNCHANGED pc

Next == Bad \/ Done

Spec == Init /\ [][Next]_pc

Inv == pc # 2
====
