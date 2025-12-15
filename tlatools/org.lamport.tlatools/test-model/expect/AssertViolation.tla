---- MODULE AssertViolation ----
EXTENDS TLC
VARIABLE v
Init == v = FALSE
Next ==
  /\ Assert(FALSE, TRUE)
  /\ v' = ~v
Spec == Init /\ [][Next]_v
====
