------ MODULE Github602 ------
EXTENDS Integers, TLC, TLCExt

VARIABLE x

Init == x = 0

A == /\ x \in Nat
     /\ x' = -x

B == x' = x + 1

Next == A \/ B

Constraint ==  x \in Nat

Inv == x >= 0

ActionConstraint == x' \in Nat

PostCondition ==
	/\ TLCSet(42, TLCGet("generated"))
	/\ ToTrace(CounterExample) = << [x |-> 0],[x |-> 1],[x |-> -1] >> 

Init2 == x = 1

PostCondition2 ==
	/\ TLCSet(42, TLCGet("generated"))
	/\ ToTrace(CounterExample) = << [x |-> 1],[x |-> -1] >> 
====

---- CONFIG Github602 ----
INIT Init
NEXT Next
CONSTRAINT Constraint
====
