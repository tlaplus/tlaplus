------------------------------- MODULE EWD998 -------------------------------
(***************************************************************************)
(* TLA+ specification of an algorithm for distributed termination          *)
(* detection on a ring, due to Shmuel Safra, published as EWD 998:         *)
(* Shmuel Safra's version of termination detection.                        *)
(* https://www.cs.utexas.edu/users/EWD/ewd09xx/EWD998.PDF                  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Functions

CONSTANT
    \* @type: Int;
    N
ASSUME NAssumption == N \in Nat \ {0} \* At least one node.

Node == 0 .. N-1
Color == {"white", "black"}
Token == [pos : Node, q : Int, color : Color]

VARIABLES 
 \* @type: Int -> Bool;
 active,     \* activation status of nodes
 \* @type: Int -> Str;
 color,      \* color of nodes
 \* @type: Int -> Int;
 counter,    \* nb of sent messages - nb of rcvd messages per node
 \* @type: Int -> Int;
 pending,    \* nb of messages in transit to node
 \* @type: [ pos: Int, q: Int, color: Str ];
 token       \* token structure
  
vars == <<active, color, counter, pending, token>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ pending \in [Node -> Nat]
  /\ token \in Token
------------------------------------------------------------------------------
 
Init ==
  (* EWD840 but nodes *) 
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  (* Rule 0 *)
  /\ counter = [i \in Node |-> 0] \* c properly initialized
  /\ pending = [i \in Node |-> 0]
  /\ token \in [ pos: Node, q: {0}, color: {"black"} ]

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
  /\ token' = [pos |-> token.pos - 1,
               q |-> token.q + counter[i],
               color |-> IF color[i] = "black" THEN "black" ELSE token.color]
            \*    color |-> color[i] ]
  /\ color' = [ color EXCEPT ![i] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter, pending>>

System == \/ InitiateProbe
          \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------

SendMsg(i) ==
  \* Only allowed to send msgs if node i is active.
  /\ active[i]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  \* Non-deterministically choose a receiver node.
  /\ \E j \in Node \ {i} : pending' = [pending EXCEPT ![j] = @ + 1]
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

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------

Next ==
  System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

(***************************************************************************)
(* Bound the otherwise infinite state space that TLC has to check.         *)
(***************************************************************************)
StateConstraint ==
  /\ \A i \in Node : counter[i] <= 2 /\ pending[i] <= 2
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

(***************************************************************************)
(* Sum of the values f[x], for x \in S \subseteq DOMAIN f.                 *)
(***************************************************************************)
Sum(f, S) == FoldFunctionOnSet(+, 0, f, S)

(***************************************************************************)
(* The number of messages on their way. "in-flight"                        *)
(***************************************************************************)
B == Sum(pending, Node)

(***************************************************************************)
(* The system has terminated if no node is active and there are no         *)
(* in-flight messages.                                                     *)
(***************************************************************************)
Termination == 
  /\ \A i \in Node : ~ active[i]
  /\ B = 0

TerminationDetection ==
  terminationDetected => Termination

(***************************************************************************)
(* Interval of nodes between a and b: this is just a..b, but the following *)
(* definition helps Apalache to construct a bounded set.                   *)
(***************************************************************************)
Rng(a,b) == { i \in Node: a <= i /\ i <= b }


(***************************************************************************)
(* Safra's inductive invariant                                             *)
(***************************************************************************)
Inv == 
  \* The number of counted messages at each node and the number of messages in transit is consistent.
  /\ P0:: B = Sum(counter, Node)
     (* (Ai: t < i < N: machine nr.i is passive) /\ *)
     (* (Si: t < i < N: ci.i) = q *)
  /\ \/ P1:: /\ \A i \in Rng(token.pos+1, N-1): active[i] = FALSE \* machine nr.i is passive
             /\ IF token.pos = N-1 
                THEN token.q = 0 
                ELSE token.q = Sum(counter, Rng(token.pos+1,N-1))
     (* (Si: 0 <= i <= t: c.i) + q > 0. *)
     \/ P2:: Sum(counter, Rng(0, token.pos)) + token.q > 0
     (* Ei: 0 <= i <= t : machine nr.i is black. *)
     \/ P3:: \E i \in Rng(0, token.pos) : color[i] = "black"
     (* The token is black. *)
     \/ P4:: token.color = "black"

(***************************************************************************)
(* The inductive invariant combined with the type invariant                *)
(***************************************************************************)
TypedInv ==
    /\ TypeOK
    /\ Inv

(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)
Liveness ==
  Termination ~> terminationDetected

(***************************************************************************)
(* The algorithm implements the specification of termination detection     *)
(* in a ring with asynchronous communication.                              *)
(* The parameters of module AsyncTerminationDetection are instantiated     *)
(* by the symbols of the same name of the present module.                  *)
(***************************************************************************)
TD == INSTANCE AsyncTerminationDetection

TDSpec == TD!Spec

THEOREM Spec => TDSpec
=============================================================================

Checked with TLC in 01/2021 with two cores on a fairly modern desktop
and the given state constraint StateConstraint above:

| N | Diameter | Distinct States | States | Time |
| --- | --- | --- | --- | --- |
| 3 | 60 | 1.3m | 10.1m | 42 s |
| 4 | 105 | 219m | 2.3b | 50 m |
