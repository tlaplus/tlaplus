---------------------------- MODULE BasicTest -------------------------------
EXTENDS Semantics

(* ID: 1 *)
op == TRUE
THEOREM RefersTo(op, "1")
THEOREM IsLevel(op, ConstantLevel)

=============================================================================
