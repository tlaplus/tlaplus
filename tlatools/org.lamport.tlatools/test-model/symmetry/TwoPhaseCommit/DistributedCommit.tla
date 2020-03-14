------------------------- MODULE DistributedCommit -------------------------
(***************************************************************************)
(* This is a high-level TLA+ specification of a distributed commit         *)
(* protocol. A set of nodes individually decide whether they wish to       *)
(* commit or abort a transaction. Second, the transaction will be          *)
(* committed iff every node wishes to commit.                              *)
(***************************************************************************)
CONSTANT Participant  \* set of participating nodes

VARIABLE pState  \* state of each participant

(***************************************************************************)
(* Possible states of non-coordinator participants.                        *)
(***************************************************************************)
PState == {"preparing", "readyCommit", "readyAbort", "committed", "aborted"}

(***************************************************************************)
(* Initially, every participant is preparing the transaction.              *)
(***************************************************************************)
Init == pState = [p \in Participant |-> "preparing"]

(***************************************************************************)
(* A participant decides whether she wishes to commit or abort.            *)
(***************************************************************************)
Decide(p) ==
  /\ pState[p] = "preparing"
  /\ \E dec \in {"readyCommit", "readyAbort"} : 
        pState' = [pState EXCEPT ![p] = dec]

(***************************************************************************)
(* A participant may definitely commit only if all participants wish       *)
(* to do so.                                                               *)
(***************************************************************************)
Commit(p) ==
  /\ \A q \in Participant : pState[q] \in {"readyCommit", "committed"}
  /\ pState' = [pState EXCEPT ![p] = "committed"]

(***************************************************************************)
(* A participant aborts if some participant wishes to do so.               *)
(***************************************************************************)
Abort(p) ==
  /\ \E q \in Participant : pState[q] \in {"readyAbort", "aborted"}
  /\ pState' = [pState EXCEPT ![p] = "aborted"]

(***************************************************************************)
(* The next-state relation is the disjunction of the above actions.        *)
(***************************************************************************)
Next ==
  \E p \in Participant : Decide(p) \/ Commit(p) \/ Abort(p)

(***************************************************************************)
(* Overall specification.                                                  *)
(***************************************************************************)
Spec == Init /\ [][Next]_pState /\ WF_pState(Next)

-----------------------------------------------------------------------------

(***************************************************************************)
(* Main safety property: participants may definitely commit only if        *)
(* all participants agree.                                                 *)
(***************************************************************************)
Safety == 
  \A p \in Participant : pState[p] = "committed" =>
     \A q \in Participant : pState[q] \in {"readyCommit", "committed"}

=============================================================================
