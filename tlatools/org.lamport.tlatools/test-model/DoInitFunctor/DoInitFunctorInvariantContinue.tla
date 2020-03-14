--------------------------- MODULE DoInitFunctorInvariantContinue ---------------------------
EXTENDS Integers

VARIABLES x
vars == <<x>>

Init == x \in 1..10

Next == x' = 0

Spec == Init /\ [][Next]_vars

(* This property is violated by all of the init states *)
Inv == x \notin Nat 
=============================================================================
