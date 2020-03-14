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
     /\ UNCHANGED d \* 18 should be covered (6 should be omitted)

B == /\ x \in Nat
     /\ UNCHANGED <<x,d>> \* 21 and 6 should be covered (6 should actually be omitted)

B2 == /\ x \in Nat
     /\ UNCHANGED vars \* 21 and 6 should be covered (6 should actually be omitted)
     
C == /\ x = 42
     /\ c' = TRUE
     /\ y' = FALSE

U1 == x < 0 /\ UNCHANGED vars \* vars should be reported as uncovered instead of x and y on line 8

U2 == x < 0 /\ UNCHANGED <<x,y>> \* col 28 & 30 

U3 == x < 0 /\ UNCHANGED x /\ UNCHANGED y \* col 26 & 41

U4 == x < 0 /\ UNCHANGED x /\ UNCHANGED d (* d itself instead of y is marked uncovered *)

UC1 == x \in Nat /\ UNCHANGED <<x,y>>

UC2 == x \in Nat /\ UNCHANGED x /\ UNCHANGED y

UC3 == x \in Nat /\ UNCHANGED vars \* Do not mark vars on line 8 as covered

Next == A \/ B \/ C \/ U1 \/ U2 \/ U3 \/ U4 \/ UC1 \/ UC2 \/ UC3

Spec == Init /\ [][Next]_vars

Constraint == x < 20

=============================================================================
