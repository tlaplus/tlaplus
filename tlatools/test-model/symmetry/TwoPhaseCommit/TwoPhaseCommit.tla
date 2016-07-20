--------------------------- MODULE TwoPhaseCommit ---------------------------
(***************************************************************************)
(* This is a TLA+ specification of the two-phase commit protocol used for  *)
(* distributed data bases. It models only one instance of the protocol,    *)
(* i.e. for a single transaction.                                          *)
(*                                                                         *)
(* We specify only the safety part of the specification: what may occur    *)
(* during an execution. This would be complemented by a specification of   *)
(* what must eventually occur, specified by suitable fairness conditions.  *)
(***************************************************************************)

CONSTANT Participant  \* set of nodes other than the coordinator

VARIABLES
  cState,     \* the state of the coordinator
  pState,     \* the state of the non-coordinator participants
  committed,  \* participants that the coordinator knows are OK for committing
  msgs        \* messages sent during the protocol

vars == <<cState, pState, committed, msgs>>

(***************************************************************************)
(* Possible states of coordinator.                                         *)
(***************************************************************************)
CState == {"preparing", "committed", "aborted"}

(***************************************************************************)
(* Possible states of non-coordinator participants.                        *)
(***************************************************************************)
PState == {"preparing", "readyCommit", "readyAbort", "committed", "aborted"}

(***************************************************************************)
(* Messages sent during the protocol.                                      *)
(***************************************************************************)
Messages ==
  \* participant informs coordinator about its decision
  [kind : {"commit", "abort"}, part : Participant] \cup
  \* coordinator tells participants whether to commit or abort
  [kind : {"doCommit", "doAbort"}]

commit(p) == [kind |-> "commit", part |-> p]
abort(p) == [kind |-> "abort", part |-> p]
doCommit == [kind |-> "doCommit"]
doAbort == [kind |-> "doAbort"]

(***************************************************************************)
(* The following predicate specifies what values the variables can take    *)
(* during an execution of the protocol.                                    *)
(***************************************************************************)
TypeOK ==
  /\ cState \in CState
  /\ pState \in [Participant -> PState]
  /\ committed \subseteq Participant
  /\ msgs \subseteq Messages
  
(***************************************************************************)
(* The initial state of the protocol.                                      *)
(***************************************************************************)
Init ==
  /\ cState = "preparing"
  /\ pState = [p \in Participant |-> "preparing"]
  /\ committed = {}
  /\ msgs = {}

(***************************************************************************)
(* The following action formulas describe the possible transitions of      *)
(* the nodes.                                                              *)
(***************************************************************************)

(***************************************************************************)
(* A participant decides and informs the coordinator of its decision.      *)
(***************************************************************************)
Decide(p) ==
  /\ pState[p] = "preparing"
  /\ \/ pState' = [pState EXCEPT ![p] = "readyCommit"] /\ msgs' = msgs \cup {commit(p)}
     \/ pState' = [pState EXCEPT ![p] = "readyAbort"] /\ msgs' = msgs \cup {abort(p)}
  /\ UNCHANGED <<cState, committed>>

(***************************************************************************)
(* A participant receives a commit or abort order from the coordinator.    *)
(***************************************************************************)
Execute(p) ==
  /\ \/ doCommit \in msgs /\ pState' = [pState EXCEPT ![p] = "committed"]
     \/ doAbort \in msgs /\ pState' = [pState EXCEPT ![p] = "aborted"]
  /\ UNCHANGED <<cState, committed, msgs>>

(***************************************************************************)
(* The coordinator receives a new commit decision for some participant.    *)
(* If all participants wish to commit, it sends an order to commit.        *)
(***************************************************************************)
RcvCommit == \E p \in Participant \ committed :
  /\ commit(p) \in msgs
  /\ committed' = committed \cup {p}
  /\ IF committed' = Participant
     THEN /\ cState' = "committed"
          /\ msgs' = msgs \cup {doCommit}
     ELSE UNCHANGED <<cState, msgs>> 
  /\ pState' = pState

(***************************************************************************)
(* The coordinator receives an abort decision and sends an order to abort. *)
(***************************************************************************)
RcvAbort == \E p \in Participant :
  /\ abort(p) \in msgs
  /\ cState' = "aborted"
  /\ msgs' = msgs \cup {doAbort}
  /\ UNCHANGED <<pState, committed>>

(***************************************************************************)
(* The overall next-state relation is the disjunction of the action        *)
(* formulas defined previously.                                            *)
(***************************************************************************)
Next ==
  \/ \E p \in Participant : Decide(p) \/ Execute(p)
  \/ RcvCommit
  \/ RcvAbort

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
-----------------------------------------------------------------------------

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)

(***************************************************************************)
(* The coordinator never sends both a doCommit and a doAbort message.      *)
(***************************************************************************)
CommitOrAbort == ~(doCommit \in msgs /\ doAbort \in msgs)

(***************************************************************************)
(* The coordinator may commit only if all participants wish to commit and  *)
(* no participant wishes to abort.                                         *)
(***************************************************************************)
AbortWins == 
  doCommit \in msgs => 
    \A p \in Participant : 
       /\ commit(p) \in msgs /\ pState[p] \in {"readyCommit", "committed"}
       /\ abort(p) \notin msgs

Liveness ==
  \A p \in Participant : <>(pState[p] \in {"committed", "aborted"})
-----------------------------------------------------------------------------

(***************************************************************************)
(* Two-phase commitment implements distributed commitment.                 *)
(***************************************************************************)
DC == INSTANCE DistributedCommit

THEOREM Spec => DC!Spec
=============================================================================
