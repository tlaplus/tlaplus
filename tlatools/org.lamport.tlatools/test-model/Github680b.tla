---- MODULE Github680b ----
VARIABLES x,y

Init == x = 0 /\ y = 0
Next == 
    /\ x' = 42
    /\ UNCHANGED <<y,x>>
====
---- CONFIG Github680b ----
INIT Init
NEXT Next
====