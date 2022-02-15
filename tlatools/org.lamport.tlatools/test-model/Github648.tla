	--------------------- MODULE Github648 -----------------------------
EXTENDS TLC, Naturals, Sequences, FiniteSets

BoundedSeqTLCEval(S, n) ==
  \* The TLCEval here must not cache the value, because it depends on the
  \* context, ie. S and n.
  UNION {TLCEval([1..m -> S]) : m \in 0..n}

ASSUME Cardinality(BoundedSeqTLCEval(BoundedSeqTLCEval({1,2}, 2), 2)) = 57

-----------------------------------------------------------------------------
BoundedSeq(S, n) ==
  UNION {[1..m -> S] : m \in 0..n}

-----------------------------------------------------------------------------
DirectedGraphs(nodes) ==
    [edge : SUBSET (nodes \X nodes)]

TestGraph ==
    \* The definition of TestGraph is evaluated multiple times.  If the def.
    \* involves TLC!RandomElement or Randomization!* the invariant Inv below
    \* will be violated *without* the TLCEval.
    TLCEval(
    	LET g == RandomElement(DirectedGraphs(1..3)) 
    	IN [ edge |-> g.edge \cup {<<1,1>>} ]
    )

-----------------------------------------------------------------------------
CONSTANT Graph

VARIABLE v, w
vars == <<v, w>>

Init ==
    /\ v \in Graph.edge
    /\ w \in Graph.edge

Next ==
    /\ v' \in Graph.edge
    /\ w' \in Graph.edge

Inv ==
    /\ v \in Graph.edge
    /\ v \in TestGraph.edge
    /\ w \in Graph.edge
    /\ w \in TestGraph.edge
    /\ TLCEval(Cardinality(
    	TLCEval(BoundedSeq(
    		TLCEval(BoundedSeq({1,2,3}, 3)), 3)))) = 65641

=============================================================================
