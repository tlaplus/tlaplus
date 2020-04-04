---------------------------- MODULE C ----------------------------
EXTENDS Naturals, FiniteSets
VARIABLES x,y

c == x
d == y

vars == <<x,y>>

a == x'

Op(S) == \A e \in SUBSET S : Cardinality(e) >= 0

Init == /\ x \in 1..3
        /\ y = 0

A == /\ c \in Nat
     /\ y \in Nat
     /\ a = x + 1
     /\ UNCHANGED y

B == /\ x \in Nat
     /\ Op(1..5)
     /\ UNCHANGED <<x,d>>

C == /\ x = 42
     /\ c' = TRUE
     /\ y' = FALSE

D == x' \in 0..x /\ UNCHANGED y

U1 == x < 0 /\ UNCHANGED vars

U2 == x < 0 /\ UNCHANGED <<x,y>>

U3 == x < 0 /\ UNCHANGED x /\ UNCHANGED y

Next == A \/ B \/ C \/ D \/ U1 \/ U2 \/ U3

Spec == Init /\ [][Next]_vars

Constraint == x < 20

(* Coverage/Cost statistics for Invariants too. *)

expensive(N) == \A e \in SUBSET (1..N) : \A f \in e : f \in 1..N 

Inv == /\ x \in Nat
       /\ y \in Nat
       /\ expensive(8)
       /\ LET frob == TRUE  
          IN /\ frob = TRUE
             /\ \A i \in 1..5: i \in Nat 
             /\ 42 \in Nat

Inv2 == /\ x \in Nat
        /\ y \in Nat
        /\ expensive(9)
        /\ LET frob == TRUE
           IN /\ frob = TRUE
             /\ \A i \in 1..5: i \in Nat 
              /\ 42 \in Nat
=============================================================================
