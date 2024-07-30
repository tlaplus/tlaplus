---- MODULE Github845 ----

VARIABLE x

Init == x = 0

A1 ==
    /\ IF FALSE
       THEN x /= 2
       ELSE TRUE
    /\ x' = 2

Next ==
    \/ A1
    \/ IF FALSE
        THEN A1
        ELSE UNCHANGED x

Spec == Init /\ [][Next]_x
====
