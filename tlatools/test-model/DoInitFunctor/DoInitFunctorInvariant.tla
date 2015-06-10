--------------------------- MODULE DoInitFunctorInvariant ---------------------------
EXTENDS Integers

VARIABLES x
vars == <<x>>

Init == x \in 1..10

Next == x' = 0

Spec == Init /\ [][Next]_vars

(* This property is violated by one of the init states *)
NotNine == x # 9 
=============================================================================
