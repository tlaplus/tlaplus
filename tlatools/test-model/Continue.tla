---- MODULE Continue ----
EXTENDS Naturals

VARIABLES x,y

Init == x = 1 /\ y = 1

Next == /\ x' = x + 1 
        /\ \/ /\ x = 1
              /\ y' \in {1,2}
           \/ /\ UNCHANGED y

\* For the test to meaningful, it is vital that workers
\* actually continue state space exploration after the
\* first invariant violation (for trace files to be written).
Inv1 == y < 2
Inv2 == x < 30

Constraint == Inv1 /\ Inv2
====
