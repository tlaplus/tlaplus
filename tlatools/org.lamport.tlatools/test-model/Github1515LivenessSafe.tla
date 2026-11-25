---- MODULE Github1515LivenessSafe ----
EXTENDS Naturals

CONSTANT Override
VARIABLE pc

F == [[i \in UNION {1..2} |-> FALSE] EXCEPT ![2] = Override]

Init == pc = 0
Next == UNCHANGED pc
Spec == Init /\ [][Next]_pc

BadLive == F[2] ~> (pc = 1)
====
