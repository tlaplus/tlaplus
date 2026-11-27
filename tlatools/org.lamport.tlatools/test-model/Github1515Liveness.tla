------------------------ MODULE Github1515Liveness -------------------------
\* https://github.com/tlaplus/tlaplus/issues/1515
EXTENDS Naturals

VARIABLE pc

F == [[i \in Nat |-> FALSE] EXCEPT ![2] = TRUE]

Init == pc = 0
Next == UNCHANGED pc
\* No fairness is needed because the expected result is a counterexample.
Spec == Init /\ [][Next]_pc

Prop == F[2] ~> FALSE
=============================================================================
