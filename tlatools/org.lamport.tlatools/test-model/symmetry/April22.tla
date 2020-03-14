----------------------------- MODULE April22 -----------------------------
EXTENDS Integers

CONSTANT S

VARIABLE x

Init == x \in S

Next == x' \in S

Spec == Init /\ [][Next]_x /\ WF_x(Next)

Live == \A i \in S : []<>(x=i)
=============================================================================
