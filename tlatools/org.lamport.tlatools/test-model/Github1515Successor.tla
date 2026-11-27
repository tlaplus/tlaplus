------------------------ MODULE Github1515Successor ------------------------
\* https://github.com/tlaplus/tlaplus/issues/1515
EXTENDS Naturals

VARIABLES pc, f
vars == <<pc, f>>

Init ==
    /\ pc = 0
    /\ f = [i \in UNION {1..2} |-> FALSE]

Create ==
    /\ pc = 0
    /\ pc' = 1
    /\ f' = [f EXCEPT ![2] = TRUE]

Use ==
    /\ pc = 1
    /\ f[2]
    /\ pc' = 2
    /\ UNCHANGED f

Stay ==
    /\ pc = 1
    /\ UNCHANGED vars

Next == Create \/ Use \/ Stay
Inv == pc # 2
\* Fingerprint <<pc, f[2]>> so the pending EXCEPT on f is not applied before Use reads f[2].
View == <<pc, f[2]>>
=============================================================================
