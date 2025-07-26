------ MODULE Github1217 ------
EXTENDS Integers

VARIABLE x

Init ==
    x = 0

Add == x' = x + 1
Sub == x' = x - 1
Reset == x' = 0

Next ==
    \/ Add
    \/ Sub
    \/ Reset

Spec == Init /\ [][Next]_<<x>>
---------------------------
=====
