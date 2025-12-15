---- MODULE Deadlock ----
VARIABLE v
Init == v = FALSE
Next == FALSE
Spec == Init /\ [][Next]_v
====
