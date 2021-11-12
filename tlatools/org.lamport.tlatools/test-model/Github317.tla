-------------------------------- MODULE Github317 --------------------------------
EXTENDS Naturals

VARIABLES a, b
vars == <<a,b>>

Init == /\ a = 0
        /\ b = 0
        
disj == /\ a' = a + 1
        /\ a' \in 1..10

Next == /\ disj
        /\ UNCHANGED b \* Moving UNCHANGED b to disj makes bug disappear (see WF_vars(...) below).

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(disj) \* disj does not define b, yet vars includes b.

Inv == ENABLED disj

Prop == <>FALSE \* Force TLC to run liveness checking.

=============================================================================
---- CONFIG Github317 ----
SPECIFICATION Spec
PROPERTY Prop
====