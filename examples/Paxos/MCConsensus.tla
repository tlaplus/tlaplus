---------------------------- MODULE MCConsensus ----------------------------- 
EXTENDS Consensus

(***************************************************************************)
(* Checking                                                                *)
(*                                                                         *)
(*      Inv /\ [Next]_chosen => Inv'                                       *)
(*                                                                         *)
(* which is equivalent to checking                                         *)
(*                                                                         *)
(*     Inv /\ [][Next]_chosen => []Inv                                     *)
(*                                                                         *)
(* which asserts that Inv is an invariant of the spec                      *)
(*                                                                         *)
(*     Inv /\ [][Next]_chosen                                              *)
(***************************************************************************)
ITypeOK == chosen \in SUBSET Value

IInv == /\ ITypeOK
        /\ Cardinality(chosen) \leq 1
          
ISpec == IInv /\ [][Next]_chosen  
=============================================================================
