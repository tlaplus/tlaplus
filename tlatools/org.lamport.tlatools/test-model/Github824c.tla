---- MODULE Github824c ----
VARIABLES var

Init == var = 0

Next ==
    /\ LET x == 1 IN var' = [field |-> <<10, x>>]
    /\ var' = [field |-> <<10, 1>>]

====
---- CONFIG Github824c ----
INIT Init
NEXT Next
====