------------------------------ MODULE I ------------------------------
EXTENDS Naturals
VARIABLES x

F[ i \in {1,2,3,4,5} ] == 
   IF i = 1 THEN 1 ELSE F[i-1] + 1 \* Recursive Function Definition

N[n \in {1,2,3}] == 
    /\ UNCHANGED <<x>>

Spec == x \in {1,2,3,4,5} /\ [][\E i \in {1,2,3} : N[i] ]_x

Inv == \E i \in DOMAIN F: F[i] = x

============
