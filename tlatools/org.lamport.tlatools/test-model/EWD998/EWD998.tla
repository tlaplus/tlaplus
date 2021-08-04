------------------------------- MODULE EWD998 -------------------------------
(***************************************************************************)
(* TLA+ specification of an algorithm for distributed termination          *)
(* detection on a ring, due to Shmuel Safra, published as EWD 998:         *)
(* Shmuel Safra's version of termination detection.                        *)
(* https://www.cs.utexas.edu/users/EWD/ewd09xx/EWD998.PDF                  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Utils

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0} \* At least one node.

Nodes == 0 .. N-1
Color == {"white", "black"}
Token == [pos : Nodes, q : Int, color : Color]

VARIABLES 
 active,     \* activation status of nodes
 color,      \* color of nodes
 counter,    \* nb of sent messages - nb of rcvd messages per node
 pending,    \* nb of messages in transit to node
 token       \* token structure
  
vars == <<active, color, counter, pending, token>>

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ counter \in [Nodes -> Int]  \* Negative, iff a node receives more messages than it sends.
  /\ pending \in [Nodes -> Nat]
  /\ token \in Token
------------------------------------------------------------------------------
 
Init ==
  (* EWD840 but nodes *) 
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  (* Rule 0 *)
  /\ counter = [i \in Nodes |-> 0] \* c properly initialized
  /\ pending = [i \in Nodes |-> 0]
  /\ token = [pos |-> 0, q |-> 0, color |-> "black"]

InitiateProbe ==
  (* Rules 1 + 5 + 6 *)
  /\ token.pos = 0
  /\ \* previous round not conclusive if:
     \/ token.color = "black"
     \/ color[0] = "black"
     \/ counter[0] + token.q > 0
  /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
  /\ color' = [ color EXCEPT ![0] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter, pending>>                            
  
PassToken(i) ==
  (* Rules 2 + 4 + 7 *)
  /\ ~ active[i] \* If machine i is active, keep the token.
  /\ token.pos = i
  /\ token' = [token EXCEPT !.pos = @ - 1,
                            !.q = @ + counter[i],
                            !.color = IF color[i] = "black" THEN "black" ELSE @]
  /\ color' = [ color EXCEPT ![i] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter, pending>>

System == \/ InitiateProbe
          \/ \E i \in Nodes \ {0} : PassToken(i)

-----------------------------------------------------------------------------

SendMsg(i) ==
  \* Only allowed to send msgs if node i is active.
  /\ active[i]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  \* Non-deterministically choose a receiver node.
  /\ \E j \in Nodes \ {i} : pending' = [pending EXCEPT ![j] = @ + 1]
          \* Note that we don't blacken node i as in EWD840 if node i
          \* sends a message to node j with j > i
  /\ UNCHANGED <<active, color, token>>

RecvMsg(i) ==
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  (* Rule 3 *)
  /\ color' = [ color EXCEPT ![i] = "black" ]
  \* Receipt of a message activates i.
  /\ active' = [ active EXCEPT ![i] = TRUE ]
  /\ UNCHANGED <<token>>                           

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, counter, pending, token>>

Environment == \E i \in Nodes : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------

Next ==
  System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

(***************************************************************************)
(* Bound the otherwise infinite state space that TLC has to check.         *)
(***************************************************************************)
StateConstraint ==
  /\ \A i \in Nodes : counter[i] <= 3 /\ pending[i] <= 3
  /\ token.q <= 3

-----------------------------------------------------------------------------

(***************************************************************************)
(* Main safety property: if there is a white token at node 0 and there are *)
(* no in-flight messages then every node is inactive.                      *)
(***************************************************************************)
terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]
  /\ pending[0] = 0

(***************************************************************************)
(* The number of messages on their way. "in-flight"                        *)
(***************************************************************************)
B == Reduce(sum, pending, 0, N-1, 0)

(***************************************************************************)
(* The system has terminated if no node is active and there are no         *)
(* in-flight messages.                                                     *)
(***************************************************************************)
Termination == 
  /\ \A i \in Nodes : ~ active[i]
  /\ B = 0

TerminationDetection ==
  terminationDetected => Termination

(***************************************************************************)
(* Safra's inductive invariant                                             *)
(***************************************************************************)
Inv == 
  /\ P0:: B = Reduce(sum, counter, 0, N-1, 0)
     (* (Ai: t < i < N: machine nr.i is passive) /\ *)
     (* (Si: t < i < N: ci.i) = q *)
  /\ \/ P1:: /\ \A i \in (token.pos+1)..N-1: ~ active[i] \* machine nr.i is passive
             /\ IF token.pos = N-1 
                THEN token.q = 0 
                ELSE token.q = Reduce(sum, counter, (token.pos+1), N-1, 0)
     (* (Si: 0 <= i <= t: c.i) + q > 0. *)
     \/ P2:: Reduce(sum, counter, 0, token.pos, 0) + token.q > 0
     (* Ei: 0 <= i <= t : machine nr.i is black. *)
     \/ P3:: \E i \in 0..token.pos : color[i] = "black"
     (* The token is black. *)
     \/ P4:: token.color = "black"

(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)
Liveness ==
  Termination ~> terminationDetected

ActionConstraint ==
    token \in Token \* Some non-constant expression that would otherwise optimized out.

=============================================================================
