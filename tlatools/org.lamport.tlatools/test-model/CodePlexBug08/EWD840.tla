------------------------------- MODULE EWD840 -------------------------------
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

Nodes == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]    \* status of nodes (active or passive)
  /\ color \in [Nodes -> Color]       \* color of nodes
  /\ tpos \in Nodes                   \* token position
  /\ tcolor \in Color                 \* token color

(* Initially the token is black. The other variables may take
   any "type-correct" values. *)
Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos \in Nodes
  /\ tcolor = "black"

(* Node 0 may initiate a probe when it has the token and
   when either it is black or the token is black. It passes
   a white token to node N-1 and paints itself white. *)
InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ active' = active
  /\ color' = [color EXCEPT ![0] = "white"]

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
  /\ tpos = i
  /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ active' = active
  /\ color' = [color EXCEPT ![i] = "white"]

(* token passing actions controlled by the termination detection algorithm *)
System == InitiateProbe \/ \E i \in Nodes \ {0} : PassToken(i)

(* An active node i may activate another node j by sending it
   a message. If j>i (hence activation goes against the direction
   of the token being passed), then node i becomes black. *)
SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Nodes \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
  /\ UNCHANGED <<tpos, tcolor>>

(* Any active node may become inactive at any moment. *)
Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>

(* actions performed by the underlying algorithm *)
Environment == \E i \in Nodes : SendMsg(i) \/ Deactivate(i)

(* next-state relation: disjunction of above actions *)
Next == System \/ Environment

vars == <<active, color, tpos, tcolor>>

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

(***************************************************************************)
(* Non-properties that can be used for validating the specification.       *)
(***************************************************************************)
TokenAlwaysBlack == tcolor = "black"

NeverChangeColor == [][ UNCHANGED color ]_vars

(***************************************************************************)
(* Main safety property: if there is a white token at node 0 then every    *)
(* node is inactive.                                                       *)
(***************************************************************************)
terminationDetected ==
  /\ tpos = 0 /\ tcolor = "white"
  /\ color[0] = "white" /\ ~ active[0]

TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~ active[i]

(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)
Liveness ==
  (\A i \in Nodes : ~ active[i]) ~> terminationDetected

(***************************************************************************)
(* The following property asserts that when every process always           *)
(* eventually terminates then eventually termination will be detected.     *)
(* It does not hold since processes can wake up each other.                *)
(***************************************************************************)
FalseLiveness ==
  \* in this version TLC displays a valid counter-example, however
  \* it prints "back to state 1" below the initial state instead of
  \* below the last state of the finite trace prefix
  (\A i \in Nodes : []<> ~ active[i]) ~> terminationDetected

FalseLiveness2 ==
  \* in this version TLC displays a counter-example that ends in
  \* infinite stuttering, which is invalid since the fairness
  \* property of the spec is not respected
  (\A i \in Nodes : (active[i] ~> ~ active[i])) ~> terminationDetected

\* This is an alternative way to express the same property: the fairness
\* condition must be added to the spec since TLC doesn't allow WF formulas
\* appearing in the property. It returns the same counter-example as the
\* first variant, with the same output problem.
Spec2 == Spec /\ \A i \in Nodes : WF_vars(Deactivate(i))
FalseLiveness3 == <>terminationDetected

(***************************************************************************)
(* The following property says that eventually all nodes will terminate    *)
(* assuming that from some point onwards no messages are sent. It is       *)
(* undesired, but verified for the fairness condition WF_vars(Next).       *)
(***************************************************************************)
Spec3 == Init /\ [][Next]_vars /\ WF_vars(Next)
AllNodesTerminateIfNoMessages ==
  ~[]<><< \E i \in Nodes : SendMsg(i) >>_vars
  => <>(\A i \in Nodes : ~ active[i])

(***************************************************************************)
(* Dijkstra's inductive invariant                                          *)
(***************************************************************************)
Inv == 
  \/ P0:: \A i \in Nodes : tpos < i => ~ active[i]
  \/ P1:: \E j \in 0 .. tpos : color[j] = "black"
  \/ P2:: tcolor = "black"

(***************************************************************************)
(* Use the following specification to check that the predicate             *)
(* TypeOK /\ Inv is inductive for EWD 840: verify that it is an            *)
(* (ordinary) invariant of a specification obtained by replacing the       *)
(* initial condition by that conjunction.                                  *)
(***************************************************************************)
CheckInductiveSpec == TypeOK /\ Inv /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Thu Apr 02 10:49:59 CEST 2015 by markus
\* Last modified Thu Apr 02 09:30:10 CEST 2015 by merz
\* Created Mon Sep 09 11:33:10 CEST 2013 by merz