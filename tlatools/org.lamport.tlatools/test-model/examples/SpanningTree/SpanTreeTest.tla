------------------------------ MODULE SpanTreeTest ------------------------------
(***************************************************************************)
(* The specification in this module is a modified version of the one in    *)
(* module SpanTree obtained by replacing the declared constant Edges with  *)
(* a variable of the same name that is set initially to any possible set   *)
(* of edges with nodes in Nodes.  Thus, it can be used to test the         *)
(* algorithm of SpanTree on all possible graphs having a particular number *)
(* of nodes.                                                               *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Randomization

CONSTANTS Nodes, Root, MaxCardinality

ASSUME /\ Root \in Nodes
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)
       
VARIABLES mom, dist, Edges
vars == <<mom, dist, Edges>>

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

TypeOK == /\ mom \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> Nat]
          /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)

Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
        /\ Edges \in {E \in SUBSET (SUBSET Nodes) : \A e \in E : Cardinality(e) = 2}
           (****************************************************************)
           (* SUBSET S is the set of all subsets of a set S.  Thus, this   *)
           (* allows Edges to have as its initial value any set of sets of *)
           (* nodes containing exactly two nodes.                          *)
           (****************************************************************)
        
Next == \E n \in Nodes :
          \E m \in Nbrs(n) : 
             /\ dist[m] < 1 + dist[n]
             /\ \E d \in (dist[m]+1) .. (dist[n] - 1) :
                    /\ dist' = [dist EXCEPT ![n] = d]
                    /\ mom'  = [mom  EXCEPT ![n] = m]
                    /\ Edges' = Edges

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
-----------------------------------------------------------------------------
PostCondition == 
  \A n \in Nodes :
    \/ /\ n = Root 
       /\ dist[n] = 0
       /\ mom[n] = n
    \/ /\ dist[n] = MaxCardinality 
       /\ mom[n] = n
       /\ \A m \in Nbrs(n) : dist[m] = MaxCardinality
    \/ /\ dist[n] \in 1..(MaxCardinality-1)
       /\ mom[n] \in Nbrs(n)
       /\ dist[n] = dist[mom[n]] + 1

Safety == []((~ ENABLED Next) => PostCondition)

Liveness == <>PostCondition
(***************************************************************************)
(* This took a few seconds to check for 4 nodes, and about 25 minutes for  *)
(* 5 nodes on my laptop.  To compute the initial value of Edges, TLC has   *)
(* to compute all the elements of SUBSET (SUBSET Nodes) (the set of all    *)
(* subsets of the set of all sets of nodes) and then throw away all the    *)
(* elements of that set that don't consist entirely of sets having         *)
(* cardinality 2.  For N nodes, SUBSET(SUBSET Nodes) contains 2^(2^N)      *)
(* elements.                                                               *)
(***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Mon Jun 17 05:43:38 PDT 2019 by lamport
\* Created Fri Jun 14 03:07:58 PDT 2019 by lamport
