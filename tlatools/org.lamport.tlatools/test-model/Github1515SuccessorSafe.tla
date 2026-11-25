---- MODULE Github1515SuccessorSafe ----
EXTENDS Naturals

CONSTANT Override
VARIABLE pc

F == [[i \in UNION {1..2} |-> FALSE] EXCEPT ![2] = Override]

Init == pc = 0

Step == pc = 0 /\ pc' = 1
Bad == pc = 1 /\ F[2] /\ pc' = 2
Done == pc = 1 /\ UNCHANGED pc

Next == Step \/ Bad \/ Done

Spec == Init /\ [][Next]_pc

Inv == pc # 2

View == pc
====
