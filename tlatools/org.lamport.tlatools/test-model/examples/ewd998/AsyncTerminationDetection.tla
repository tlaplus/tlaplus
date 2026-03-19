---------------------- MODULE AsyncTerminationDetection ---------------------
(***************************************************************************)
(* An abstract specification of the termination detection problem in a     *)
(* ring with asynchronous communication.                                   *)
(***************************************************************************)
EXTENDS Naturals
CONSTANT
  \* @type: Int; 
  N
ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES 
  \* @type: Int -> Bool;
  active,               \* activation status of nodes
  \* @type: Int -> Int;
  pending,              \* number of messages pending at a node
  \* @type: Bool;
  terminationDetected   \* has termination been detected?

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ pending \in [Node -> Nat]
  /\ terminationDetected \in BOOLEAN

terminated == \A n \in Node : ~ active[n] /\ pending[n] = 0

(***************************************************************************)
(* Initial condition: the nodes can be active or inactive, no pending      *)
(* messages. Termination may (but need not) be detected immediately if all *)
(* nodes are inactive.                                                     *)
(***************************************************************************)
Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ pending = [n \in Node |-> 0]
  /\ terminationDetected \in {FALSE, terminated}

Terminate(i) ==  \* node i terminates
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ pending' = pending
     (* possibly (but not necessarily) detect termination if all nodes are inactive *)
  /\ terminationDetected' \in {terminationDetected, terminated'}

SendMsg(i,j) ==  \* node i sends a message to node j
  /\ active[i]
  /\ pending' = [pending EXCEPT ![j] = @ + 1]
  /\ UNCHANGED <<active, terminationDetected>>

RcvMsg(i) == \* node i receives a pending message
  /\ pending[i] > 0
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  /\ UNCHANGED terminationDetected

DetectTermination ==
  /\ terminated
  /\ terminationDetected' = TRUE
  /\ UNCHANGED <<active, pending>>

Next ==
  \/ \E i \in Node : RcvMsg(i) \/ Terminate(i)
  \/ \E i,j \in Node : SendMsg(i,j)
  \/ DetectTermination

vars == <<active, pending, terminationDetected>>
Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(DetectTermination)
           \* reasonable but not necessary for detecting termination
           \* /\ \A i \in Node : WF_vars(Wakeup(i))

\* a temporary solution for Apalache, until it translates [][Next]_vars
NextOrUnchanged ==
    Next \/ UNCHANGED vars

(***************************************************************************)
(* Restrict TLC model checking to a finite fragment of the state space.    *)
(***************************************************************************)
StateConstraint == \A n \in Node : pending[n] <= 3

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
Safe == terminationDetected => terminated

Quiescence == [](terminated => []terminated)

Live == terminated ~> terminationDetected

(***************************************************************************)
(* An inductive invariant to be checked with Apalache.                     *)
(***************************************************************************)
IndInv ==
    /\ TypeOK
    /\ Safe

\* By proving QuiescenceAsActionInv, we show that Quiescence holds true
QuiescenceAsActionInv ==
    terminated => terminated'

\* @typeAlias: STATE =
\*   [ active: Int -> Bool, pending: Int -> Int, terminationDetected: Bool ];
\* @type: Seq(STATE) => Bool;
QuiescenceAsTraceInv(hist) ==
    LET terminatedAt(i) ==
        \A n \in Node: ~hist[i].active[n] /\ hist[i].pending[n] = 0
    IN
    \A i \in DOMAIN hist:
        terminatedAt(i) =>
            \A j \in DOMAIN hist: j >= i => terminatedAt(j)

(***************************************************************************)
(* Use Apalache to verify Quiescence by checking the action formula        *)
(* StableActionInvariant for a model with initial-state predicate TypeOK   *)
(* and next-state relation Next.                                           *)
(***************************************************************************)
StableActionInvariant == terminated => terminated'
=============================================================================
\* Modification History
\* Last modified Tue Apr 12 15:04:08 CEST 2022 by merz
\* Last modified Wed Jun 02 14:21:31 PDT 2021 by markus
\* Created Sun Jan 10 15:19:20 CET 2021 by merz
