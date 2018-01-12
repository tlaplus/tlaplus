
------------------------------- MODULE EWD840 -------------------------------

EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor
vars == <<active, color, tpos, tcolor>>

Nodes == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]    \* status of nodes (active or passive)
  /\ color \in [Nodes -> Color]       \* color of nodes
  /\ tpos \in Nodes                   \* token position
  /\ tcolor \in Color                 \* token color

(* Initially the token is at node 0, and it is black. There
   are no constraints on the status and color of the nodes. *)
Init ==
  /\ active \in [Nodes -> BOOLEAN] \* Array of nodes to boolean mappings, initially all false
  /\ color \in [Nodes -> Color]    \* Array of nodes to (node) color mappings, initially all white
  /\ tpos = 0
  /\ tcolor = "black"

(* Node 0 may initiate a probe when it has the token and
   when either it is black or the token is black. This is
   necessary to terminate once a conclusive round has ended.
   It passes a white token to node N-1 and paints itself white. *)
InitiateProbe ==
  /\ tpos = 0          \* Initially the token is a the 0 node
  /\ tcolor = "black" \/ color[0] = "black"  \* Prevent the master node from starting another round after it has received a positive result (termination) in the previous round. 
                                             \* Note that TLC will terminate even without this condition, it won't show algorithm termination represented by a deadlock though. 
  /\ tpos' = N-1       \* In the next state the token is at node N-1
  /\ tcolor' = "white" \* In the next state the token color is white
  /\ color' = [color EXCEPT ![0] = "white"] \* node colors are preserved/unchanged, except of node 0 (who initiated the probe)
  /\ UNCHANGED <<active>>  \* The active states are preservered/unchanged in the next state

(* A node i different from 0 that possesses the token may pass
   it to node i-1 under the following circumstances:
   - node i is inactive or
   - node i is colored black or
   - the token is black.
   Note that the last two conditions will result in an
   inconclusive round, since the token will be black.
   The token will be stained if node i is black, otherwise 
   its color is unchanged. Node i will be made white. *)
PassToken(i) ==
  /\ tpos = i   \* Node i can only pass the token if it posses it
  /\ ~ active[i] \* Node i is inactive
        \/ color[i] = "black" \* Node i has been marked stained already
        \/ tcolor = "black"   \* The token has been stained by a higher node already
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active>>

(* An active node i may activate another node j by sending it
   a message. If j>i (hence activation goes against the direction
   of the token being passed), then node i becomes black. *)
SendMsg(i) ==
  /\ active[i]  \* Only allowed to send msgs if node i is active
  /\ \E j \in Nodes \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
  /\ UNCHANGED <<tpos, tcolor>>

(* Any active node may become inactive at any moment. *)
Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>

(* next-state relation: disjunction of above actions *)
Next ==
  \/ InitiateProbe
  \/ \E i \in Nodes \ {0} : PassToken(i)
  \/ \E i \in Nodes : SendMsg(i) \/ Deactivate(i)

(* Actions controlled by termination detection algorithm *)
System ==
  \/ InitiateProbe
  \/ \E i \in Nodes \ {0} : PassToken(i)

Fairness == WF_vars(System)

Spec == Init /\ [][Next]_vars /\ Fairness

LInv == [][Next]_vars => WF_vars(System)

-----------------------------------------------------------------------------

(***************************************************************************)
(* Non-invariants that can be used for validating the specification.       *)
(***************************************************************************)
NeverBlack == \A i \in Nodes : color[i] # "black"

NeverChangeColor == [][ \A i \in Nodes : UNCHANGED color[i] ]_vars

(***************************************************************************)
(* Main safety property: if there is a white token at node 0 then every    *)
(* node is inactive.                                                       *)
(***************************************************************************)
terminationDetected ==
  /\ tpos = 0 /\ tcolor = "white"
  /\ color[0] = "white" /\ ~ active[0]
  /\ color[1] = "white"

TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~ active[i]
(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)
Liveness ==
  /\ (\A i \in Nodes : ~ active[i]) ~> terminationDetected

(***************************************************************************)
(* The following property says that eventually all nodes will terminate    *)
(* assuming that from some point onwards no messages are sent. It is       *)
(* undesired, but verified for the fairness condition WF_vars(Next).       *)
(* This motivates weakening the fairness condition to WF_vars(System).     *)
(***************************************************************************)
AllNodesTerminateIfNoMessages ==
  <>[][~ \E i \in Nodes : SendMsg(i)]_vars
  => <>(\A i \in Nodes : ~ active[i])

(***************************************************************************)
(* Dijkstra's inductive invariant                                          *)
(***************************************************************************)
Inv ==
  \/ P0:: \A i \in Nodes : tpos < i => ~ active[i]
  \/ P1:: \E j \in 0 .. tpos : color[j] = "black"
  \/ P2:: tcolor = "black"

=============================================================================
\* Modification History
\* Last modified Wed Sep 06 18:13:33 CEST 2017 by markus
\* Last modified Tue Jun 10 09:50:24 CEST 2014 by merz
\* Created Mon Sep 09 11:33:10 CEST 2013 by merz
