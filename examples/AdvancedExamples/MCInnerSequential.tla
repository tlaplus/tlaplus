--------------------- MODULE MCInnerSequential -----------------------
EXTENDS InnerSequential

CONSTANT MaxQLen
Constraint == \A p \in Proc : Len(opQ[p]) \leq MaxQLen

AlwaysResponds == 
  (*************************************************************************)
  (* A simple liveness property, implied by the fact that every request    *)
  (* eventually generates a response.                                      *)
  (*************************************************************************)
  \A p \in Proc, r \in Reg :
       (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")
=============================================================================

