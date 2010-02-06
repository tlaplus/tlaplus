---------------------------- MODULE TLAProofRules --------------------------- 
(***************************************************************************)
(* This file defines two fundamental TLA proof rules.  Full                *)
(* temporal-logic reasoning is not yet implemented in the TLA+ Proof       *)
(* System.  However, these two proof rules are enough to handle proofs of  *)
(* safety properties for specs that don't use hiding (temporal             *)
(* existential quantification).                                            *)
(***************************************************************************)
THEOREM Inv1 == ASSUME STATE I, STATE f,  ACTION N,
                       I /\ [N]_f => I'
                PROVE  I /\ [][N]_f => []I 
PROOF OMITTED
                
THEOREM StepSimulation == ASSUME STATE I, STATE f, STATE g, 
                                 ACTION M, ACTION N,
                                 I /\ [M]_f => [N]_g
                          PROVE  []I /\ [][M]_f => [][N]_g  
PROOF OMITTED

(***************************************************************************)
(* We now mysteriously state a rather obvious theorem.  The mystery is     *)
(* explained by the comment that follows the statement of the theorem.  It *)
(* is a pragma that tells the Proof System to interpret any reference to   *)
(* SimpleArithmetic as a fact in a leaf proof to be an instruction to      *)
(* perform the proof by applying Cooper's algorithm, which is a decision   *)
(* procedure for a class of arithmetic formulas.                           *)
(***************************************************************************)
THEOREM SimpleArithmetic == TRUE    (*{by (cooper) }*)
OBVIOUS
=============================================================================
\* Generated at Fri Nov 06 14:29:58 PST 2009