---- MODULE ExitStatus ----
EXTENDS TLC
VARIABLE x
Init == x = 0
BadInit == x = 2
Next == x = 0 /\ x' = 1
BadNext == x = 0 /\ x' = 2
AssertNext == x = 0 /\ x' = 1 /\ Assert(FALSE, "worker assertion failed")
Inv == x # 2
====
