---------------------------- MODULE CoverageStatistics ----------------------------
EXTENDS Naturals, FiniteSets
VARIABLES x,y

c == x
d == y

vars == <<x,y>>

a == x'

Init == /\ x \in 1..3
        /\ y = 0

A == /\ c \in Nat
     /\ y \in Nat
     /\ a = x + 1
     /\ UNCHANGED y

B == /\ x \in Nat
     /\ UNCHANGED <<x,d>>

C == /\ x = 42
     /\ c' = TRUE
     /\ y' = FALSE

U1 == x < 0 /\ UNCHANGED vars

U2 == x < 0 /\ UNCHANGED <<x,y>>

U3 == x < 0 /\ UNCHANGED x /\ UNCHANGED y

Next == A \/ B \/ C \/ U1 \/ U2 \/ U3

Spec == Init /\ [][Next]_vars

Constraint == x < 20

=============================================================================
