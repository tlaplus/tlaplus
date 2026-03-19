----------------------------- MODULE YoYoNoPruning ---------------------------
(****************************************************************************)
(* TLA+ specification of the Yo-Yo leader election algorithm in arbitrary   *)
(* undirected graphs without self-loops. The algorithm was introduced by    *)
(* Nicola Santoro, cf. "Design and Analysis of Distributed Algorithms",     *)
(* section 3.8.3, see also https://en.wikipedia.org/wiki/Yo-yo_(algorithm). *)
(* The algorithm assumes that nodes are (identified by) integers, and the   *)
(* node with the smallest identity will be elected leader.                  *)
(*                                                                          *)
(* The algorithm orients the edges of the graph. Initially, all edges are   *)
(* directed from smaller to larger node identities, so sources correspond   *)
(* to local minima in their neighborhoods and sinks correspond to local     *)
(* maxima. Sources are considered candidates for being leader, and as long  *)
(* as their are at least two sources, each round will eliminate at least    *)
(* one of them.                                                             *)
(*                                                                          *)
(* Each round consists of two phases, traditionally called the "Yo-" and    *)
(* "-Yo" phases, that will be called "down" and "up" phases below.          *)
(* The down phase is initiated by the sources, which broadcast their        *)
(* identity to all neighbors. Non-source nodes wait for values to have been *)
(* received from all incoming neighbors, then broadcast the minimum value   *)
(* that has been received to all outgoing neighbors. (Sink nodes do not     *)
(* send messages in the down phase.)                                        *)
(*                                                                          *)
(* The up phase is initiated by sink nodes when they have received values   *)
(* from all neighbors in the down phase. They reply "yes" to all neighbors  *)
(* that sent the minimum value and "no" to all other neighbors. The other   *)
(* nodes wait until messages for the up phase have been received from all   *)
(* outgoing neighbors. If one message is "no", they send "no" to all        *)
(* incoming neighbors, otherwise they send "yes" to those incoming          *)
(* neighbors who sent the smallest value during the down phase and "no" to  *)
(* all other incoming neighbors. (Source nodes do not send messages in the  *)
(* up phase.)                                                               *)
(* Moreover, edges along which a "no" message is sent during the up phase   *)
(* change orientation. This may change the status of a node (source,        *)
(* sink or internal).                                                       *)
(*                                                                          *)
(* The algorithm stabilizes in a state where there is at most one source,   *)
(* after which point only the identity of that source will be sent during   *)
(* the down phase and only "yes" messages will be sent during the up phase. *)
(* However, no node detects termination. Ensuring termination of the        *)
(* algorithm is achieved by pruning the graph, modeled in a variant of the  *)
(* present specification.                                                   *)
(*                                                                          *)
(* Authors: Ludovic Yvoz and Stephan Merz, 2024.                            *)
(****************************************************************************)

EXTENDS TLC, Integers, FiniteSets, UndirectedGraphs

CONSTANT Nodes, Edges   \* the nodes and edges of the graph

ASSUME  
  (* nodes are represented by their integer identities *)
  /\ Nodes \subseteq Int
  /\ Nodes # {} 
  /\ LET G == [node |-> Nodes, edge |-> Edges]
     IN  /\ IsUndirectedGraph(G)
         /\ IsStronglyConnected(G)

Neighbors(n) == {m \in Nodes : {m,n} \in Edges}

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

VARIABLES 
  (* the phase (down or up) each node is currently executing *)
  phase,
  (* incoming and outgoing neighbors of each node *)
  incoming, outgoing,
  (* mailbox of each node *)
  mailbox

vars == <<phase, incoming, outgoing, mailbox>>

(****************************************************************************)
(* Determine the kind of the node: source, sink or internal.                *)
(****************************************************************************)
kind(n) ==
    IF incoming[n] = {} THEN "source"
    ELSE IF outgoing[n] = {} THEN "sink"
    ELSE "internal"

(****************************************************************************)
(* Messages sent during the algorithm.                                      *)
(****************************************************************************)
Messages == 
  [phase : {"down"}, sndr : Nodes, val : Nodes] \cup  
  [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}]
downMsg(s,v) == [phase |-> "down", sndr |-> s, val |-> v]
upMsg(s,r) == [phase |-> "up", sndr |-> s, reply |-> r]

(****************************************************************************)
(* Type correctness predicate.                                              *)
(****************************************************************************)
TypeOK == 
    /\ phase \in [Nodes -> {"down", "up"}]
    /\ incoming \in [Nodes -> SUBSET Nodes]
    /\ \A n \in Nodes : incoming[n] \subseteq Neighbors(n)
    /\ outgoing \in [Nodes -> SUBSET Nodes]
    /\ \A n \in Nodes : outgoing[n] \subseteq Neighbors(n)
    /\ mailbox \in [Nodes -> SUBSET Messages]
    /\ \A n \in Nodes : \A msg \in mailbox[n] :
          /\ msg.phase = "down" => 
             /\ n \in outgoing[msg.sndr]
             /\ \A mm \in mailbox[n] : \* at most one message per neighbor
                   mm.phase = "down" /\ mm.sndr = msg.sndr => mm = msg
          /\ msg.phase = "up" => 
             /\ msg.sndr \in outgoing[n]
             /\ \A mm \in mailbox[n] : \* at most one message per neighbor
                   mm.phase = "up" /\ mm.sndr = msg.sndr => mm = msg

------------------------------------------------------------------------------
(****************************************************************************)
(* Yo-Yo algorithm as a state machine.                                      *)
(****************************************************************************)
Init == 
    /\ phase = [n \in Nodes |-> "down"]
    /\ incoming = [n \in Nodes |-> { m \in Neighbors(n) : m < n}]
    /\ outgoing = [n \in Nodes |-> { m \in Neighbors(n) : m > n}]
    /\ mailbox = [n \in Nodes |-> {}]

------------------------------------------------------------------------------
(****************************************************************************)
(* Down phase: we distinguish sources and other nodes.                      *)
(* Note that a node retains "down" messages after executing the phase       *)
(* because they are used during the up phase.                               *)
(****************************************************************************)
DownSource(n) == 
    /\ kind(n) = "source"
    /\ phase[n] = "down"
    /\ mailbox' = [m \in Nodes |-> 
        IF m \in outgoing[n] THEN mailbox[m] \cup {downMsg(n,n)}
        ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<incoming, outgoing>>

DownOther(n) == 
    /\ kind(n) \in {"internal", "sink"}
    /\ phase[n] = "down"
    /\ LET downMsgs == {msg \in mailbox[n] : msg.phase = "down"}
       IN  /\ {msg.sndr : msg \in downMsgs} = incoming[n]
           /\ LET min == Min({msg.val : msg \in downMsgs})
              IN mailbox' = [m \in Nodes |->
                             IF m \in outgoing[n] 
                             THEN mailbox[m] \cup {downMsg(n,min)}
                             ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<incoming, outgoing>>

Down(n) == DownSource(n) \/ DownOther(n)

------------------------------------------------------------------------------
(****************************************************************************)
(* Up phase, again distinguishing sources and other nodes.                  *)
(*                                                                          *)
(* An internal or source node may already have received "down" messages     *)
(* for the following round from neighbors that it still considers as        *)
(* outgoing neighbors but for which the edge direction was reversed.        *)
(* We therefore have to be careful to only consider "down" messages from    *)
(* neighbors that the node considers as incoming, and also to preserve      *)
(* "down" messages for the following round when cleaning the mailbox.       *)
(****************************************************************************)
UpSource(n) ==
    /\ kind(n) = "source"
    /\ phase[n] = "up"
    /\ LET upMsgs == {msg \in mailbox[n] : msg.phase = "up"}
           noSndrs == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
       IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
           /\ mailbox' = [mailbox EXCEPT ![n] = mailbox[n] \ upMsgs]
           /\ incoming' = [incoming EXCEPT ![n] = noSndrs]
           /\ outgoing' = [outgoing EXCEPT ![n] = @ \ noSndrs]
    /\ phase' = [phase EXCEPT ![n] = "down"]

UpOther(n) ==
    /\ kind(n) \in {"internal", "sink"}
    /\ phase[n] = "up"
    /\ LET upMsgs == {msg \in mailbox[n] : msg.phase = "up"}
           noSndrs == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
           downMsgs == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
       IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]  \* always true for sinks
           /\ IF noSndrs = {}  \* true in particular for sinks
              THEN LET min == Min({msg.val : msg \in downMsgs})
                       minSndrs == {msg.sndr : msg \in {mm \in downMsgs : mm.val = min}}
                   IN  /\ mailbox' = [m \in Nodes |->
                             IF m \in incoming[n]
                             THEN mailbox[m] \union 
                                    {upMsg(n, IF m \in minSndrs THEN "yes" ELSE "no")}
                             ELSE IF m = n THEN mailbox[m] \ (upMsgs \union downMsgs)
                             ELSE mailbox[m]]
                       /\ incoming' = [incoming EXCEPT ![n] = minSndrs]
                       /\ outgoing' = [outgoing EXCEPT ![n] = 
                                           @ \union (incoming[n] \ minSndrs)]
              ELSE /\ mailbox' = [m \in Nodes |->
                        IF m \in incoming[n] THEN mailbox[m] \union {upMsg(n, "no")}
                        ELSE IF m = n THEN mailbox[m] \ (upMsgs \union downMsgs)
                        ELSE mailbox[m]]
                   /\ incoming' = [incoming EXCEPT ![n] = noSndrs]
                   /\ outgoing' = [outgoing EXCEPT ![n] = 
                                        (@ \ noSndrs) \union incoming[n]]
    /\ phase' = [phase EXCEPT ![n] = "down"]

Up(n) == UpSource(n) \/ UpOther(n)

------------------------------------------------------------------------------

Next == \E n \in Nodes : Down(n) \/ Up(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

------------------------------------------------------------------------------
(****************************************************************************)
(* Formulas used for verification.                                          *)
(****************************************************************************)

(****************************************************************************)
(* Predicate asserting that there will always be at least two source nodes. *)
(* Checking this as an invariant produces an execution that shows that all  *)
(* sources except for the leader will be eliminated.                        *)
(****************************************************************************)
MoreThanOneSource == \E s1, s2 \in Nodes :
    s1 # s2 /\ kind(s1) = "source" /\ kind(s2) = "source"

(****************************************************************************)
(* Node m is an outgoing neighbor of node n iff n is an incoming neighbor   *)
(* of m, except if the edge is being reversed, in which case there is a     *)
(* "no" message in one of the mailboxes.                                    *)
(****************************************************************************)
NeighborInv == \A m,n \in Nodes :
  m \in outgoing[n] <=> 
    \/ n \in incoming[m]
    \/ /\ n \in outgoing[m] 
       /\ upMsg(n, "no") \in mailbox[m] \/ upMsg(m, "no") \in mailbox[n]

(****************************************************************************)
(* No new sources are generated during execution of the algorithm.          *)
(****************************************************************************)
NoNewSource == 
  [][\A n \in Nodes : kind(n)' = "source" => kind(n) = "source"]_vars

(****************************************************************************)
(* Stabilization condition: there is only one source node, all "down"       *)
(* messages carry the identity of that node, all "up" messages say "yes".   *)
(****************************************************************************)
Stabilization ==
    /\ kind(Min(Nodes)) = "source"
    /\ \A n \in Nodes : kind(n) = "source" => n = Min(Nodes)
    /\ \A n \in Nodes : \A msg \in mailbox[n] : 
          /\ msg.phase = "down" => msg.val = Min(Nodes)
          /\ msg.phase = "up" => msg.reply = "yes"

Liveness == <>[]Stabilization
==============================================================================