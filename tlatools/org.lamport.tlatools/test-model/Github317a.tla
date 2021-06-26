-------------------------------- MODULE Github317a --------------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
ro, n1, n2, n3, n4, n5

Nodes==
{ro, n1, n2, n3, n4, n5}

root==
ro

Edges==
{{ro,n1}, {ro,n2}, {n1,n3}, {n2,n3}, {n3,n4}, {n3,n5}}

MaxNodes==
7

HasTwoElts(S) == \E a,b \in S : (a # b) /\ (S = {a,b})

ASSUME /\ \A e \in Edges : (e \subseteq Nodes) /\ HasTwoElts(e)
       /\ root \in Nodes
       /\ MaxNodes >= Cardinality(Nodes)

Nbrs(n) == {m \in Nodes : {m,n} \in Edges}

SetNbrs(S) == UNION {Nbrs(n) : n \in S}

RECURSIVE ReachableFrom(_)
ReachableFrom(S) == LET R == SetNbrs(S)
                    IN  IF R \subseteq S THEN S
                                         ELSE ReachableFrom(R \cup S)
                          
RECURSIVE DistanceFrom(_, _)
DistanceFrom(n, S) == IF n \in S THEN 0 
                                 ELSE 1 + DistanceFrom(n, S \cup SetNbrs(S))
----------------------------------------------------------------------------
(***************************************************************************)
(* More efficiently executable definitions.                                *)
(***************************************************************************)

RECURSIVE EReachableFrom(_,_)
EReachableFrom(Bdry, S) ==
   LET R == SetNbrs(Bdry) \ S                            
   IN  IF R = {} THEN S ELSE EReachableFrom(R, R\cup S)

THEOREM \A S \in SUBSET Nodes : EReachableFrom(S, {}) = ReachableFrom(S)

ASSUME ReachableFrom({root}) = Nodes

RECURSIVE EDistanceFrom(_, _, _)
EDistanceFrom(n, Bdry, S) ==
     LET R == SetNbrs(Bdry) \ S
     IN  IF n \in Bdry THEN 0 ELSE 1 + EDistanceFrom(n, R, S \cup R)
     
THEOREM \A n \in Nodes, S \in (SUBSET Nodes) \ {{}} : 
         EDistanceFrom(n, S, {}) = DistanceFrom(n, S)

Dist(n, m) == EDistanceFrom(n, {m}, {})
-----------------------------------------------------------------------------
QueuesFrom(n) == {<<n, m>> : m \in Nbrs(n)}
QueuesTo(n)  == {<<m, n>> : m \in Nbrs(n)}
Queues == UNION {QueuesFrom(n) : n \in Nodes}
NodePs == {<<n>> : n \in Nodes}

(***************************************************************************
--algorithm MinSpanningTree {
    variables msgs = [q \in Queues |-> IF q[1] = root THEN <<0>> ELSE << >>] ;
    fair process (nd \in NodePs) 
      variables depth = IF self[1] = root THEN 0 ELSE MaxNodes,
                parent = self[1], 
                acked = [n \in Nbrs(self[1]) |->  
                           IF self[1] = <<root>> THEN FALSE ELSE TRUE];           
      { a: while (TRUE) { 
\*            either {
              with (q \in {r \in QueuesTo(self[1]) : msgs[r] /= << >>}) {
                 if (Head(msgs[q]) < depth - 1) {
                    depth := Head(msgs[q]) + 1;
                    parent := q[1] ;
                    msgs := [r \in Queues |->
                              IF r = q 
                                THEN Tail(msgs[q])
                                ELSE IF r \in QueuesFrom(self[1]) \ {<<self[1], q[1]>>}
                                       THEN Append(msgs[r], depth)
                                       ELSE msgs[r] ];
                   acked := [b \in Nbrs(self[1]) |-> b /= q[1]] 
                              
                 } else { 
                     msgs[q] := Tail(msgs[q]) ;
                     if (Head(msgs[q]) =< depth+1) {acked[q[1]] := TRUE} 
                 }
               }
\*           }
         }
      }
\*    process (qu \in Queues) {
\*   }
}

 ***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "702f848" /\ chksum(tla) = "c301c684")
VARIABLES msgs, depth, parent, acked

vars == << msgs, depth, parent, acked >>

ProcSet == (NodePs)

Init == (* Global variables *)
        /\ msgs = [q \in Queues |-> IF q[1] = root THEN <<0>> ELSE << >>]
        (* Process nd *)
        /\ depth = [self \in NodePs |-> IF self[1] = root THEN 0 ELSE MaxNodes]
        /\ parent = [self \in NodePs |-> self[1]]
        /\ acked = [self \in NodePs |-> [n \in Nbrs(self[1]) |->
                                           IF self[1] = <<root>> THEN FALSE ELSE TRUE]]

nd(self) == \E q \in {r \in QueuesTo(self[1]) : msgs[r] /= << >>}:
              IF Head(msgs[q]) < depth[self] - 1
                 THEN /\ depth' = [depth EXCEPT ![self] = Head(msgs[q]) + 1]
                      /\ parent' = [parent EXCEPT ![self] = q[1]]
                      /\ msgs' = [r \in Queues |->
                                   IF r = q
                                     THEN Tail(msgs[q])
                                     ELSE IF r \in QueuesFrom(self[1]) \ {<<self[1], q[1]>>}
                                            THEN Append(msgs[r], depth'[self])
                                            ELSE msgs[r] ]
                      /\ acked' = [acked EXCEPT ![self] = [b \in Nbrs(self[1]) |-> b /= q[1]]]
                 ELSE /\ msgs' = [msgs EXCEPT ![q] = Tail(msgs[q])]
                      /\ IF Head(msgs'[q]) =< depth[self]+1
                            THEN /\ acked' = [acked EXCEPT ![self][q[1]] = TRUE]
                            ELSE /\ TRUE
                                 /\ acked' = acked
                      /\ UNCHANGED << depth, parent >>

Next == (\E self \in NodePs: nd(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in NodePs : WF_vars(nd(self))

\* END TRANSLATION 

TypeOK == /\ depth  \in [NodePs -> 0..MaxNodes]
          /\ parent \in [NodePs -> Nodes]
          /\ msgs \in [Queues -> Seq(0..(Cardinality(Nodes)-1))]
          
Termination == \A q \in Queues : msgs[q] = << >>

Correctness == Termination => 
                 \A n \in Nodes : 
                    /\ depth[<<n>>] = Dist(n, root)
                    /\ (n /= root) => depth[<<parent[<<n>>]>>] = depth[<<n>>] - 1

Prop ==
<>Termination
    
=============================================================================
---- CONFIG Github317a ----
CONSTANTS
ro = ro
n1 = n1
n2 = n2
n3 = n3
n4 = n4
n5 = n5

SPECIFICATION
Spec

INVARIANT
TypeOK
Correctness

PROPERTY
Prop
====