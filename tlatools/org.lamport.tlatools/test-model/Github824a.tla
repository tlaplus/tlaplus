---- MODULE Github824a ----
VARIABLES var

Init ==
    /\ LET x == 1 IN var = x
    /\ var = 1

Next == UNCHANGED var

====
---- CONFIG Github824a ----
INIT Init
NEXT Next
====