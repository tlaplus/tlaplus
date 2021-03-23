---- CONFIG IncompatibleTypesLive ----
SPECIFICATION 
    Spec
PROPERTIES
    Prop
====

---- MODULE IncompatibleTypesLive ----
EXTENDS Naturals

VARIABLES x

Init == x = 0

Next == 
    \/ x' \in 1..100 \* Need to create enough successors for SetOfState to exhibit collisions.
    \/ x' = FALSE 
    \/ x' = "abc"

Spec == Init /\ [][Next]_x

Prop == <>[]TRUE
=====