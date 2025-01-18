---------------------------- MODULE AssumeTest ------------------------------
EXTENDS Semantics

(* ID: def *)
ASSUME def == TRUE
THEOREM RefersTo(def, "def")
THEOREM IsLevel(def, ConstantLevel)

(* ID: def2 *)
ASSUMPTION def2 == TRUE
THEOREM RefersTo(def2, "def2")
THEOREM IsLevel(def2, ConstantLevel)

(* ID: def3 *)
AXIOM def3 == TRUE
THEOREM RefersTo(def3, "def3")
THEOREM IsLevel(def3, ConstantLevel)

=============================================================================
