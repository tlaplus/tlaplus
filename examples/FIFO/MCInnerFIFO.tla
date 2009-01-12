--------------------------- MODULE MCInnerFIFO -----------------------------

(***************************************************************************)
(* To run TLC on module InnerFIFOInstanced, we need to define an           *)
(* additional operator.  We don't want to modify module InnerFIFOInstanced *)
(* for the benefit of TLC, so we put the definition in this module, which  *)
(* EXTENDS module InnerFIFOInstanced.                                      *)
(*                                                                         *)
(* The specification Spec of module InnerFIFO has an unbounded number of   *)
(* reachable states, since the queue q can become arbitrarily large.  To   *)
(* model-check the specification, we have to constrain the set of states   *)
(* examined by TLC to be finite.  We do this by telling TLC to look only   *)
(* at states in which q has a fixed maximum length.  We define qConstraint *)
(* to be a state predicate asserting this constraint, and tell TLC (with   *)
(* the configuration file) to use qConstraint as a constraint.             *)
(***************************************************************************)
EXTENDS InnerFIFOInstanced

CONSTANT qLen
  (*************************************************************************)
  (* Instead of putting a fixed maximum length for q in the definition of  *)
  (* qConstraint, we let that maximum length be the constant qLen.  We     *)
  (* assign a value to qLen in the configuration file.  This allows us to  *)
  (* control the size of the model we check by changing only the           *)
  (* configuration file.                                                   *)
  (*************************************************************************)

qConstraint == Len(q) \leq qLen
  (*************************************************************************)
  (* This is the predicate constraining the length of q.                   *)
  (*************************************************************************)
=============================================================================