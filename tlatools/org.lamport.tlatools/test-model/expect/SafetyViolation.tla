---- MODULE SafetyViolation ----
VARIABLE v
Init == v = TRUE
Next == v' = ~v
Safety == v
Spec == Init /\ [][Next]_v
====
