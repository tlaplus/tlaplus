---- MODULE Github680a ----
VARIABLES x

Init == x = 0
Next == 
    /\ x' = 42
    /\ UNCHANGED <<x>>
====
---- CONFIG Github680a ----
INIT Init
NEXT Next
====