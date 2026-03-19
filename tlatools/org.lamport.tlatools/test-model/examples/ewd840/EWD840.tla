------------------------------- MODULE EWD840 -------------------------------
(***************************************************************************)
(* TLA+ specification of an algorithm for distributed termination          *)
(* detection on a ring, due to Dijkstra, published as EWD 840:             *)
(* Derivation of a termination detection algorithm for distributed         *)
(* computations (with W.H.J.Feijen and A.J.M. van Gasteren).               *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

Node == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Node -> BOOLEAN]    \* status of nodes (active or passive)
  /\ color \in [Node -> Color]       \* color of nodes
  /\ tpos \in Node                   \* token position
  /\ tcolor \in Color                 \* token color

(***************************************************************************)
(* Initially the token is black. The other variables may take any          *)
(* "type-correct" values.                                                  *)
(***************************************************************************)
Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ tpos \in Node
  /\ tcolor = "black"

(***************************************************************************)
(* Node 0 may initiate a probe when it has the token and when either it is *)
(* black or the token is black. It passes a white token to node N-1 and    *)
(* paints itself white.                                                    *)
(***************************************************************************)
InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ active' = active
  /\ color' = [color EXCEPT ![0] = "white"]

(***************************************************************************)
(* A node i different from 0 that possesses the token may pass it to node  *)
(* i-1 under the following circumstances:                                  *)
(*   - node i is inactive or                                               *)
(*   - node i is colored black or                                          *)
(*   - the token is black.                                                 *)
(* Note that the last two conditions will result in an inconclusive round, *)
(* since the token will be black. The token will be stained if node i is   *)
(* black, otherwise its color is unchanged. Node i will be made white.     *)
(***************************************************************************)
PassToken(i) == 
  /\ tpos = i
  /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ active' = active
  /\ color' = [color EXCEPT ![i] = "white"]

(***************************************************************************)
(* token passing actions controlled by the termination detection algorithm *)
(***************************************************************************)
System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

(***************************************************************************)
(* An active node i may activate another node j by sending it a message.   *)
(* If j>i (hence activation goes against the direction of the token being  *)
(* passed), then node i becomes black.                                     *)
(***************************************************************************)
SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Node \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
  /\ UNCHANGED <<tpos, tcolor>>

(***************************************************************************)
(* Any active node may become inactive at any moment.                      *)
(***************************************************************************)
Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>

(***************************************************************************)
(* actions performed by the underlying algorithm                           *)
(***************************************************************************)
Environment == \E i \in Node : SendMsg(i) \/ Deactivate(i)

(***************************************************************************)
(* next-state relation: disjunction of above actions                       *)
(***************************************************************************)
Next == System \/ Environment

vars == <<active, color, tpos, tcolor>>

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

(***************************************************************************)
(* Non-properties, useful for validating the specification with TLC.       *)
(***************************************************************************)
TokenAlwaysBlack == tcolor = "black"

NeverChangeColor == [][ UNCHANGED color ]_vars

(***************************************************************************)
(* Main safety property: if there is a white token at node 0 then every    *)
(* node is inactive.                                                       *)
(***************************************************************************)
terminated == \A i \in Node : ~ active[i]

terminationDetected ==
  /\ tpos = 0 /\ tcolor = "white"
  /\ color[0] = "white" /\ ~ active[0]

TerminationDetection == terminationDetected => terminated

(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)
Liveness == terminated ~> terminationDetected

(***************************************************************************)
(* The following property asserts that when every process always           *)
(* eventually terminates then eventually termination will be detected.     *)
(* It does not hold since processes can wake up each other.                *)
(***************************************************************************)
FalseLiveness ==
  (\A i \in Node : []<> ~ active[i]) ~> terminationDetected

(***************************************************************************)
(* The following property says that eventually all nodes will terminate    *)
(* assuming that from some point onwards no messages are sent. It is       *)
(* not supposed to hold: any node may indefinitely perform local           *)
(* computations. However, this property is verified if the fairness        *)
(* condition WF_vars(Next) is used instead of only WF_vars(System) that    *)
(* requires fairness of the actions controlled by termination detection.   *)
(***************************************************************************)
SpecWFNext == Init /\ [][Next]_vars /\ WF_vars(Next)
AllNodesTerminateIfNoMessages ==
  <>[][\A i \in Node : ~ SendMsg(i)]_vars => <>(\A i \in Node : ~ active[i])

(***************************************************************************)
(* Dijkstra's inductive invariant                                          *)
(***************************************************************************)
Inv == 
  \/ P0:: \A i \in Node : tpos < i => ~ active[i]
  \/ P1:: \E j \in 0 .. tpos : color[j] = "black"
  \/ P2:: tcolor = "black"

(***************************************************************************)
(* Use the following specification to let TLC check that the predicate     *)
(* TypeOK /\ Inv is inductive for EWD 840: verify that it is an            *)
(* (ordinary) invariant of a specification obtained by replacing the       *)
(* initial condition by that conjunction.                                  *)
(***************************************************************************)
CheckInductiveSpec == TypeOK /\ Inv /\ [][Next]_vars

(***************************************************************************)
(* The algorithm implements the high-level specification of termination    *)
(* detection in a ring with synchronous communication between nodes.       *)
(* Note that the parameters of the module SyncTerminationDetection are     *)
(* instantiated by the symbols of the same name in the present module.     *)
(***************************************************************************)
TD == INSTANCE SyncTerminationDetection
TDSpec == TD!Spec
=============================================================================
\* Modification History
\* Created Mon Sep 09 11:33:10 CEST 2013 by merz
