---- MODULE Github971 ----
EXTENDS Integers
VARIABLE x

Init ==
    x = -1

Next ==
    x' \in {0,1} 

Spec == 
    Init /\ [][Next]_x

AtMostOnce==
    []((x=1) => []((x=0) => [](x=0)))

==========================
