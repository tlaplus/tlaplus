------------------------ MODULE LiveInternalMemory --------------------------

(***************************************************************************)
(* This module defines LISpec to be specification ISpec of module          *)
(* InternalMemory enhanced with the liveness condition described in the    *)
(* subsection "The Liveness Requirement" of the section "The Memory        *)
(* Specification".                                                         *)
(***************************************************************************)

EXTENDS InternalMemory

vars == <<memInt, mem, ctl, buf>>
  (*************************************************************************)
  (* The tuple of all variables.                                           *)
  (*************************************************************************)
  
Liveness == \A p \in Proc : WF_vars(Do(p)) /\ WF_vars(Rsp(p))
Liveness2 == \A p \in Proc : WF_vars(Do(p) \/ Rsp(p))
  (*************************************************************************)
  (* The two versions of the liveness condition defined in the book.       *)
  (*************************************************************************)
  
LISpec == ISpec /\ Liveness2
  (*************************************************************************)
  (* The spec with liveness.                                               *)
  (*************************************************************************)

(***************************************************************************)
(* The following property asserts that, whenever any processor p has       *)
(* issued a request, so ctl[p] = "req", then a response eventually occurs, *)
(* setting ctl[p] to "rdy".                                                *)
(***************************************************************************)

LivenessProperty == 
   \A p \in Proc : (ctl[p] = "req") ~> (ctl[p] = "rdy")

-----------------------------------------------------------------------------
(***************************************************************************)
(* The following theorem asserts that specification LISpec satisfies       *)
(* property LivenessProperty.  The accompanying configuration file has TLC *)
(* check this theorem.                                                     *)
(***************************************************************************)

THEOREM LISpec => LivenessProperty
=============================================================================
