------------------------------- MODULE MTest6 ------------------------------- 

(* Generate TLC error when checking temporal properties after finding all
    reachable states.
Model 1: Property false.
*)
EXTENDS Naturals
VARIABLE x, y
Init == x=0 /\ y=0
Next == x'=x /\ y'=1-y

         
=============================================================================
