---- MODULE Github971 ----

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
