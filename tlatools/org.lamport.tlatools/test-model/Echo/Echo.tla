-------------------------------- MODULE Echo --------------------------------
(***************************************************************************)
(* The Echo algorithm for constructing a spanning tree in an undirected    *)
(* graph starting from a single initiator, as a PlusCal algorithm.         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Relation, TLC

CONSTANTS Node,      \* set of nodes
          initiator, \* single initiator, will be the root of the tree
          R          \* neighborhood relation, represented as a Boolean function over nodes 

ASSUME /\ initiator \in Node
       /\ R \in [Node \X Node -> BOOLEAN]
       \* No edge from a node to itself (self-loops).
       /\ IsIrreflexive(R, Node)
       \* Undirected graph (there exists an edge from b 
       \* to a if there exists an edge from a to b).
       /\ IsSymmetric(R, Node)
       \* There exists a spanning tree consisting of *all* nodes.
       \* (no forest of spanning trees). 
       /\ IsConnected(R, Node)

NoNode == CHOOSE x : x \notin Node
neighbors(n) == { m \in Node : R[m,n] }

(**
--algorithm Echo {
    variable inbox = [n \in Node |-> {}];  \* model communication between nodes
    define { \* sending and receiving messages
      \* network obtained from net when p sends message of kind knd to q
      send(net, p, q, knd) == [net EXCEPT ![q] = @ \cup {[kind |-> knd, sndr |-> p]}]
      \* network obtained from net when p receives a message
      receive(net, p, msg) == [net EXCEPT ![p] = @ \ {msg}]
      \* network obtained from net when p send message of kind knd to all nodes in dest
      multicast(net, p, dest, knd) ==
        [m \in Node |-> IF m \in dest THEN net[m] \cup {[kind |-> knd, sndr |-> p]}
                        ELSE net[m]]
    }

  process (node \in Node) 
    variables parent = NoNode,
              children = {},
              rcvd = 0,
              nbrs = neighbors(self);        {
  n0: if (self = initiator) {
         \* initiator sends first message to all its neighbors
         inbox := multicast(inbox, self, nbrs, "m")
      };
  n1: while (rcvd < Cardinality(nbrs)) {
         \* receive some message from a neighbor
         with (msg \in inbox[self],
               net = receive(inbox, self, msg)) {
            rcvd := rcvd+1;
            if (self # initiator /\ rcvd = 1) {
               assert(msg.kind = "m");  \* the first received message is always of type "m"
               \* note the sender as the node's parent and send an "m" message to all remaining neighbors
               parent := msg.sndr;
               inbox := multicast(net, self, nbrs \ {msg.sndr}, "m")
            }
            else {
               \* subsequent messages are counted but don't give rise to another message
               inbox := net
            };
            if (msg.kind = "c") { children := children \cup {msg.sndr} }
         }  \* end with
      }; \* end while
  n2: if (self # initiator) {
         \* when non-initiator has received messages from all neighbors, acknowledge
         \* child relationship to the parent
         assert(parent \in nbrs);
         inbox := send(inbox, self, parent, "c")
      }
  } \* end process
}
**)
\* BEGIN TRANSLATION
VARIABLES inbox, pc

(* define statement *)
send(net, p, q, knd) == [net EXCEPT ![q] = @ \cup {[kind |-> knd, sndr |-> p]}]

receive(net, p, msg) == [net EXCEPT ![p] = @ \ {msg}]

multicast(net, p, dest, knd) ==
  [m \in Node |-> IF m \in dest THEN net[m] \cup {[kind |-> knd, sndr |-> p]}
                  ELSE net[m]]

VARIABLES parent, children, rcvd, nbrs

vars == << inbox, pc, parent, children, rcvd, nbrs >>

ProcSet == (Node)

Init == (* Global variables *)
        /\ inbox = [n \in Node |-> {}]
        (* Process node *)
        /\ parent = [self \in Node |-> NoNode]
        /\ children = [self \in Node |-> {}]
        /\ rcvd = [self \in Node |-> 0]
        /\ nbrs = [self \in Node |-> neighbors(self)]
        /\ pc = [self \in ProcSet |-> "n0"]

n0(self) == /\ pc[self] = "n0"
            /\ IF self = initiator
                  THEN /\ inbox' = multicast(inbox, self, nbrs[self], "m")
                  ELSE /\ TRUE
                       /\ inbox' = inbox
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED << parent, children, rcvd, nbrs >>

n1(self) == /\ pc[self] = "n1"
            /\ IF rcvd[self] < Cardinality(nbrs[self])
                  THEN /\ \E msg \in inbox[self]:
                            LET net == receive(inbox, self, msg) IN
                              /\ rcvd' = [rcvd EXCEPT ![self] = rcvd[self]+1]
                              /\ IF self # initiator /\ rcvd'[self] = 1
                                    THEN /\ Assert((msg.kind = "m"), 
                                                   "Failure of assertion at line 50, column 16.")
                                         /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                                         /\ inbox' = multicast(net, self, nbrs[self] \ {msg.sndr}, "m")
                                    ELSE /\ inbox' = net
                                         /\ UNCHANGED parent
                              /\ IF msg.kind = "c"
                                    THEN /\ children' = [children EXCEPT ![self] = children[self] \cup {msg.sndr}]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED children
                       /\ pc' = [pc EXCEPT ![self] = "n1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
                       /\ UNCHANGED << inbox, parent, children, rcvd >>
            /\ nbrs' = nbrs

n2(self) == /\ pc[self] = "n2"
            /\ IF self # initiator
                  THEN /\ Assert((parent[self] \in nbrs[self]), 
                                 "Failure of assertion at line 65, column 10.")
                       /\ inbox' = send(inbox, self, parent[self], "c")
                  ELSE /\ TRUE
                       /\ inbox' = inbox
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << parent, children, rcvd, nbrs >>

node(self) == n0(self) \/ n1(self) \/ n2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node: node(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
TypeOK ==
  /\ parent \in [Node -> (Node \cup {NoNode})]
  /\ children \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> Nat]
  /\ nbrs \in [Node -> SUBSET Node]
  /\ \A n \in Node : nbrs[n] = neighbors(n) /\ rcvd[n] <= Cardinality(nbrs[n])
  /\ inbox \in [Node -> SUBSET [kind : {"m","c"}, sndr : Node]]
  /\ \A n \in Node : \A msg \in inbox[n] : msg.sndr \in nbrs[n]


(* The initiator never has a parent *)
InitiatorNoParent == parent[initiator] = NoNode

(* If a node has a parent, it is a neighbor node *)
ParentIsNeighbor == \A n \in Node : parent[n] \in neighbors(n) \cup {NoNode}

(* A node n is a child of node m only if m is the parent of n.
   At the end of the computation, this is "if and only if". *)
ParentChild == \A m,n \in Node :
  /\ n \in children[m] => m = parent[n]
  /\ m = parent[n] /\ pc[m] = "Done" => n \in children[m]

(* Compute the ancestor relation *)
IsParent == [m,n \in Node |-> n = parent[m]]
IsAncestor == TransitiveClosure(IsParent, Node)

(* At the end of the computation, the initiator is an ancestor of every other node
   and the ancestor relation is acyclic.
   Beware: evaluating this property over any but tiny graphs is costly.
*)
AncestorProperties ==
  (\A n \in Node : pc[n] = "Done")
  => LET anc == IsAncestor
     IN  /\ \A n \in Node \ {initiator} : anc[n, initiator]
         /\ IsIrreflexive(anc, Node)

=============================================================================
\* Modification History
\* Last modified Wed Jun 17 09:23:17 PDT 2020 by markus
\* Last modified Sun Jun 14 17:11:39 CEST 2020 by merz
\* Created Tue Apr 26 09:42:23 CEST 2016 by merz
