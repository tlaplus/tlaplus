---------------- MODULE TraceWithLargeSetOfInitialStatesTest ----------------
EXTENDS Integers

VARIABLES x,y

Spec == (x \in 1..11 /\ y = FALSE) /\ [][x' = x /\ y' = TRUE]_<<x,y>>

Inv == y = FALSE
=============================================================================