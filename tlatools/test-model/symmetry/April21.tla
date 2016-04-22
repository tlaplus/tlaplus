----------------------------- MODULE April21 -----------------------------
EXTENDS Integers

CONSTANT S

VARIABLE x

Init == x \in S

Next == x' \in S

Spec == Init /\ [][Next]_x

Live == \E i \in S : <>[][x # i]_x
=============================================================================
