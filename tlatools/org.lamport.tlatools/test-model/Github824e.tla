---- MODULE Github824e ----
EXTENDS Naturals

VARIABLES var

Init == var = 0

Next ==
    /\ (LET x == var' IN ENABLED (x = 1 /\ var < 1)) = ENABLED (var' = 1 /\ var < 1)
    /\ var' = 1
====
---- CONFIG Github824e ----
INIT Init
NEXT Next
====