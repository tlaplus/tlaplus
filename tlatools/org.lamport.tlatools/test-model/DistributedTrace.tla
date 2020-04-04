-------------------------- MODULE DistributedTrace --------------------------
EXTENDS Integers, Sequences

VARIABLES x
vars == <<x>>

Init == x \in 1..10

Next == x' = x + 1

Spec == /\ Init /\ [][Next]_vars

Inv == x < 20
=============================================================================
