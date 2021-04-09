------ MODULE Github602 ------
EXTENDS Integers

VARIABLE x

Init == x = 0

A == /\ x \in Nat
     /\ x' = -x

B == x' = x + 1

Next == A \/ B

Constraint ==  x \in Nat
====

---- CONFIG Github602 ----
INIT Init
NEXT Next
CONSTRAINT Constraint
====
