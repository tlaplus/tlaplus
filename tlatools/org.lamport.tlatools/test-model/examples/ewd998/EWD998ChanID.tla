---------------------------- MODULE EWD998ChanID ----------------------------
(***************************************************************************)
(* This spec differs from EWD998Chan in that:                              *)
(*  - Where EWD998Chan (and EWD998) use naturals to model nodes, this spec *)
(*    uses a kind of identifier such as strings.  The identifiers are      *)
(*    organized into a ring.                                               *)
(*                                                                         *)
(*  - The initiator of tokens no longer is node 0 but an arbitrarily       *)
(*    chosen one.                                                         *)
(*                                                                         *)
(*  - The payload message "pl" contains the message sender "src".          *)
(*                                                                         *)
(* Minor differences:                                                      *)
(*  - In the interest of conciseness, the spec drops a few definitions     *)
(*    that are found in the high-level spec EWD998Chan.                    *)
(*                                                                         *)
(*  - Pull \E n \in Nodes up to the Spec level in preparation of PlusPy    *)
(*    implementation.                                                      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Naturals, Utils

Merge(n, r, l) ==
    LET max(a, b) == IF a > b THEN a ELSE b
    IN [ m \in DOMAIN l |-> IF m = n THEN l[m] + 1 ELSE max(r[m], l[m]) ]

CONSTANT Node
ASSUME IsFiniteSet(Node) /\ Node # {}

N == Cardinality(Node)

\* Choose a node to be the initiator of a fresh token. We don't care which one it
\* is as long as it is always the same.
Initiator == CHOOSE n \in Node : TRUE
                                         
\* Organize Nodes in a ring. 
RingOfNodes == 
  CHOOSE r \in [ Node -> Node ]: IsSimpleCycle(Node, r)
  
nat2node[ i \in 0..N-1 ] ==
    IF i = 0 THEN Initiator ELSE AntiFunction(RingOfNodes)[nat2node[i-1]]

node2nat ==
    AntiFunction(nat2node)

Color == {"white", "black"}

VARIABLES 
 active,
 color,
 counter,
 inbox,
 clock,
 passes
  
vars == <<active, color, counter, inbox, clock, passes>>

terminated ==
    \A n \in Node :
        /\ ~ active[n]
        \* Count the in-flight "pl" messages. The 
        \* inbox variable represents a node's network
        \* interface that receives arbitrary messages.
        \* However, EWD998 only "tracks" payload (pl)
        \* messages.
        /\ [m \in Node |-> 
                Len(SelectSeq(inbox[m], 
                    LAMBDA msg: msg.type = "pl")) ][n] = 0

terminationDetected ==
  /\ \E j \in 1..Len(inbox[Initiator]):
        /\ inbox[Initiator][j].type = "tok"
        /\ inbox[Initiator][j].color = "white"
        /\ inbox[Initiator][j].q + counter[Initiator] = 0
  /\ color[Initiator] = "white"
  /\ ~ active[Initiator]

------------------------------------------------------------------------------
 
Init ==
  (* Each node maintains a (local) vector clock *)
  (* https://en.wikipedia.org/wiki/Vector_clock *)
  /\ clock = [ n \in Node |-> IF n = Initiator 
                THEN [ m \in Node |-> IF m = Initiator THEN 1 ELSE 0 ]
                ELSE [ m \in Node |-> 0 ] ]
  (* Rule 0 *)
  /\ counter = [n \in Node |-> 0] \* c properly initialized
\*   /\ inbox = [n \in Node |-> IF n = Initiator 
\*                               THEN << [type |-> "tok", q |-> 0, color |-> "black", vc |-> clock[n] ] >> 
\*                               ELSE <<>>] \* with empty channels.
\* The token may be at any node of the ring initially.
\*   /\ inbox \in { f \in 
\*                     [ Node -> {<<>>, <<[type |-> "tok", q |-> 0, color |-> "black", vc |-> clock[Initiator] ]>> } ] : 
\*                         Cardinality({ i \in DOMAIN f: f[i] # <<>> }) = 1 }
\* Worst-case WRT Max3TokenRounds, token is at node N-2.
  /\ inbox = [n \in Node |-> IF n = nat2node[N-2] 
                              THEN << [type |-> "tok", q |-> 0, color |-> "black", vc |-> clock[n] ] >> 
                              ELSE <<>>] \* with empty channels.
  (* EWD840 *) 
  /\ active \in [Node -> {FALSE}]
  /\ color \in [Node -> {"black"}]
  /\ passes = IF terminated THEN 0 ELSE -1

InitiateProbe(n) ==
  /\ n = Initiator
  (* Rule 1 *)
  /\ \E j \in 1..Len(inbox[Initiator]):
      \* Token is at node the Initiator.
      /\ inbox[Initiator][j].type = "tok"
      /\ clock' = [clock EXCEPT ![n] = Merge(n, inbox[n][j].vc, @)]
      /\ \* Previous round inconsistent, if:
         \/ inbox[Initiator][j].color = "black"
         \/ color[Initiator] = "black"
         \* Implicit stated in EWD998 as c0 + q > 0 means that termination has not 
         \* been achieved: Initiate a probe if the token's color is white but the
         \* number of in-flight messages is not zero.
         \/ counter[Initiator] + inbox[Initiator][j].q # 0
      /\ inbox' = [inbox EXCEPT ![RingOfNodes[Initiator]] = Append(@, 
           [type |-> "tok", q |-> 0,
             (* Rule 6 *)
             color |-> "white", vc |-> clock[n]']), 
             ![Initiator] = RemoveAt(@, j) ] \* consume token message from inbox[0]. 
  (* Rule 6 *)
  /\ color' = [ color EXCEPT ![Initiator] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter>>
  /\ passes' = IF passes >= 0 THEN passes + 1 ELSE passes
  
PassToken(n) ==
  /\ n # Initiator
  (* Rule 2 *)
  /\ ~ active[n] \* If machine i is active, keep the token.
  /\ \E j \in 1..Len(inbox[n]) : 
          /\ inbox[n][j].type = "tok"
          /\ clock' = [clock EXCEPT ![n] = Merge(n, inbox[n][j].vc, @)]
          \* the machine nr.i+1 transmits the token to machine nr.i under q := q + c[i+1]
          /\ LET tkn == inbox[n][j]
             IN  inbox' = [inbox EXCEPT ![RingOfNodes[n]] = 
                                       Append(@, [tkn EXCEPT !.q = tkn.q + counter[n],
                                                             !.color = IF color[n] = "black"
                                                                       THEN "black"
                                                                       ELSE tkn.color,
                                                             !.vc = clock[n]' ]),
                                    ![n] = RemoveAt(@, j) ] \* pass on the token.
  (* Rule 7 *)
  /\ color' = [ color EXCEPT ![n] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter>>                            
  /\ passes' = IF passes >= 0 THEN passes + 1 ELSE passes

System(n) == \/ InitiateProbe(n)
             \/ PassToken(n)
 
-----------------------------------------------------------------------------

SendMsg(n) ==
  \* Only allowed to send msgs if node i is active.
  /\ active[n]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![n] = @ + 1]
  /\ clock' = [ clock EXCEPT ![n][n] = @ + 1 ]
  \* Non-deterministically choose a receiver node.
  /\ \E j \in Node \ {n} :
          \* Send a message (not the token) to j.
          /\ inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl", src |-> n, vc |-> clock[n]' ] ) ]
          \* Note that we don't blacken node i as in EWD840 if node i
          \* sends a message to node j with j > i
  /\ UNCHANGED <<active, color, passes>>

\* RecvMsg could write the incoming message to a (Java) buffer from which the (Java) implementation consumes it. 
RecvMsg(n) ==
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![n] = @ - 1]
  (* Rule 3 *)
  /\ color' = [ color EXCEPT ![n] = "black" ]
  \* Receipt of a message activates node n.
  /\ active' = [ active EXCEPT ![n] = TRUE ]
  \* Consume a message (not the token!).
  /\ \E j \in 1..Len(inbox[n]) : 
          /\ inbox[n][j].type = "pl"
          /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j) ]
          /\ clock' = [ clock EXCEPT ![n] = Merge(n, inbox[n][j].vc, @) ]
  /\ UNCHANGED passes

Deactivate(n) ==
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ clock' = [ clock EXCEPT ![n][n] = @ + 1 ]
  /\ UNCHANGED <<color, inbox, counter>>
  /\ passes' = IF terminated' THEN 0 ELSE passes

Environment(n) == 
  \/ SendMsg(n)
  \/ RecvMsg(n)
  \/ Deactivate(n)

-----------------------------------------------------------------------------

Next(n) ==
  System(n) \/ Environment(n)

\* Idiomatic/canonical TLA+ has existential quantification down in System and Next.
Spec == Init /\ [][\E n \in Node: Next(n)]_vars
             /\ \A n \in Node: WF_vars(System(n))

Max3TokenRounds ==
    \* Termination is detected within a maximum of three token rounds after the
    \* system is terminated.
    passes <= 3 * N

THEOREM Spec => []Max3TokenRounds

-----------------------------------------------------------------------------
\* The definitions of the refinement mapping below this line will be
\* ignored by PlusPy.  It can thus make use of RECURSIVE.
\*++:Spec

a \prec b ==
    \* True iff node a is a predecessor of node b in the ring.
    node2nat[a] < node2nat[b]

a ++ b ==
    \* The set of nodes between node a and node b (inclusive) in the ring.
    LET i == node2nat[a]
        j == node2nat[b]
    IN { nat2node[k] : k \in i..j }

Node2Nat(fcn) ==
  [ i \in 0..N-1 |->  fcn[nat2node[i]] ]

MapSeq(seq, Op(_)) ==
    LET F[i \in 0..Len(seq)] == IF i = 0
                                THEN << >>
                                ELSE Append(F[i - 1], Op(seq[i]))
    IN F[Len(seq)]

EWD998ChanInbox ==
    \* Drop the src and the vc from the payload message.
    [n \in DOMAIN inbox |->
        MapSeq(inbox[n], 
            LAMBDA m: 
            IF m.type = "pl" 
            THEN [type |-> "pl"] 
            ELSE IF m.type = "tok"
                 THEN [type |-> "tok", q |-> m.q, color |-> m.color]
                 ELSE m) 
    ]

(***************************************************************************)
(* EWD998ChanID (identifier) refines EWD998Chan where nodes are modelled   *)
(* with naturals \in 0..N-1. To check that EWD998ChanID is a correct       *)
(* refinement _and_ to save us the troubles of rewriting the (inductive)   *)
(* Inv for identifiers, we have TLC check the two theorems below.          *)
(***************************************************************************)
EWD998Chan == INSTANCE EWD998Chan WITH active <- Node2Nat(active),
                                        color <- Node2Nat(color),
                                      counter <- Node2Nat(counter),
                                        inbox <- Node2Nat(EWD998ChanInbox)

EWD998ChanStateConstraint == EWD998Chan!StateConstraint
EWD998ChanSpec == EWD998Chan!Spec

THEOREM Spec => EWD998ChanSpec

EWD998Safe == EWD998Chan!EWD998!TD!Safe
EWD998Live == EWD998Chan!EWD998!TD!Live

THEOREM Spec => EWD998Safe /\ EWD998Live
-----------------------------------------------------------------------------

\* The (vector) clock is not relevant for the correctness of the algorithm.
View == 
    <<active, color, counter, EWD998ChanInbox, passes>>

=============================================================================
