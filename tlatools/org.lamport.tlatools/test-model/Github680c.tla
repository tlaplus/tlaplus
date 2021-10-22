---- MODULE Github680c ----
VARIABLES x,y

Init == x = 0 /\ y = 0
Next == 
    /\ y' = 0
    /\ x' = 42
    /\ UNCHANGED <<y,x>>
====
---- CONFIG Github680c ----
INIT Init
NEXT Next
====