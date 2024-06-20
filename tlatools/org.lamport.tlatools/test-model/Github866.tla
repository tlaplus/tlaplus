---- MODULE Github866 ----

VARIABLE x

Init ==
    x = FALSE

Next ==
    x' \in BOOLEAN 

Spec == 
    Init /\ [][Next]_x

AtMostOnce==
    [](x => [](~x => []~x))

==========================

---- CONFIG Github866 ----
SPECIFICATION Spec
PROPERTY AtMostOnce
====
