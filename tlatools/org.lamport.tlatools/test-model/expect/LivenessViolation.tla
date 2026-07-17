---- MODULE LivenessViolation ----
VARIABLE v
Init == v = FALSE
Next == v' = ~v
Liveness == <>v
Spec == Init /\ [][Next]_v
====
