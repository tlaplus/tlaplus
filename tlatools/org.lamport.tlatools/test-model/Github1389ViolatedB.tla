--------------------------- MODULE Github1389ViolatedB ---------------------------
EXTENDS Naturals

VARIABLE x

RECURSIVE Reach(_)
Reach(n) == IF n = 0 THEN (x = 99) ELSE <>(Reach(n - 1))

Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)

PropViolated == Reach(3)
==================================================================
