--------------------------- MODULE DoInitFunctorEvalException ---------------------------
EXTENDS Integers

VARIABLES x
vars == <<x>>

Init == x \in 1..10

Next == x' = 0

Spec == Init /\ [][Next]_vars

(* This function is used as a model constraint to trigger an EvalException (because it doesn't return Bool) *)
F(a) == {}
const_4711 == F(x)

(* This property is violated by one of the init states *)
NotNine == x # 9 
=============================================================================
