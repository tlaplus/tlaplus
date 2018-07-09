------------------ MODULE DoInitFunctorMinimalErrorStack --------------------
EXTENDS Naturals

VARIABLES a, b
vars == <<a, b>>

Init == 
  /\ a \in [1..2 -> 1..3]
  /\ b = TRUE

Spec == Init /\ [][UNCHANGED vars]_vars

(* This property is violated by all of the init states *)
Inv == a >= 0
=============================================================================
