------------------------------ MODULE MCVoting ------------------------------
EXTENDS Voting, TLC

CONSTANTS a1, a2, a3  \* acceptors
CONSTANTS v1, v2      \* Values

MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == {{a1, a2}, {a1, a3}, {a2, a3}}
MCBallot == 0..1
MCSymmetry == Permutations(MCAcceptor) \cup Permutations(MCValue)

(***************************************************************************)
(* The various formulas given to TLC through the configuration file must   *)
(* consist of single identifiers.  Thus, to get TLC to check that the      *)
(* specification satisfies (implements) C!Spec, we cannot put              *)
(*                                                                         *)
(*    PROPERTY C!Spec                                                      *)
(*                                                                         *)
(* in the configuration file.  We therefore define ConsensusSpecBar to     *)
(* equal it and put                                                        *)
(*                                                                         *)
(*    PROPERTY ConsensusSpecBar                                            *)
(*                                                                         *)
(* in the configuration file.                                              *)
(***************************************************************************)
ConsensusSpecBar == C!Spec

(***************************************************************************)
(* The following assumption checks theorem QuorumNonEmpty                  *)
(***************************************************************************)
ASSUME QuorumNonEmpty!:

MCInit == TypeOK

(***************************************************************************)
(* Checking that MCInv is an invariant of MCSpec checks the correctness of *)
(* theorems AllSafeAtZero through ShowsSafety.                             *)
(***************************************************************************)
MCSpec == TypeOK /\ [][FALSE]_<<votes, maxBal>>
MCInv == /\ AllSafeAtZero!:
         /\ ChoosableThm!:
         /\ OneValuePerBallot => OneVote
         /\ VotesSafeImpliesConsistency!:
         /\ ShowsSafety!:

(***************************************************************************)
(* Checking that Inv is an invariant of MCSpecI checks that Inv is         *)
(* an inductive invariant--that is, it checks                              *)
(*                                                                         *)
(*   THEOREM Inv /\ [Next]_<<votes, maxBal>>  =>  Inv'                     *)
(***************************************************************************)
MCSpecI == Inv /\ [][Next]_<<votes, maxBal>>

=============================================================================
