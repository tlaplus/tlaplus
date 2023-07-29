---- MODULE Github824d ----
VARIABLES var

Init == var = 0

Next ==
    /\ LET x == (var' = 1) IN x
    /\ var' = 1

====
---- CONFIG Github824d ----
INIT Init
NEXT Next
====