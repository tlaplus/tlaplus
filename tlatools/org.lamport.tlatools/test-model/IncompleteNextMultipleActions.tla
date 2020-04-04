--------------------------- MODULE IncompleteNextMultipleActions ---------------------------
EXTENDS Integers, TLC

VARIABLES x, y, z

A1 == x'= x + 1

A2 == x'= 1 /\ y' = 1 /\ z' = 1

Spec == (x=0) /\ (y=0) /\ (z=0) /\ [][A1 \/ A2]_<<x,y,z>>
=============================================================================
