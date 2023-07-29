---- MODULE Github824b ----
VARIABLES var

Init == var = 0

Next ==
    /\ LET x == 1 IN var' = x
    /\ var' = 1

====
---- CONFIG Github824b ----
INIT Init
NEXT Next
====