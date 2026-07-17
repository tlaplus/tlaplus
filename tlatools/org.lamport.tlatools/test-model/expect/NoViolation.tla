---- MODULE NoViolation ----
VARIABLE v
Init == v = FALSE
Next == v' = ~v
Spec == Init /\ [][Next]_v
====
