---- MODULE ExitStatus ----
VARIABLE x
Init == x = 0
BadInit == x = 2
Next == x = 0 /\ x' = 1
BadNext == x = 0 /\ x' = 2
Inv == x # 2
====
