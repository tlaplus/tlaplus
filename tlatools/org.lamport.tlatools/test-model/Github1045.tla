---- MODULE Github1045 ----
EXTENDS Naturals

Max(a, b) == IF a > b THEN a ELSE b
SetMin(S) == CHOOSE e \in S : \A o \in S : e <= o
Transpose(F) == SetMin({F[n][o] : n, o \in DOMAIN F})

CONSTANT Node

VARIABLE counter

Convergence == []<>(\A n, o \in Node : counter[n] = counter[o])

Init == counter = [n \in Node |-> [o \in Node |-> 0]]

Increment(n) ==
  counter' = [counter EXCEPT ![n][n] = @ + 1]

Gossip(n, o) ==
  counter' = [
    counter EXCEPT ![o] = [
      nodeView \in Node |->
        Max(counter[n][nodeView], counter[o][nodeView])
      ]
    ]

Next ==
  \/ \E n \in Node : Increment(n)
  \/ \E n, o \in Node : Gossip(n, o)

Spec ==
  /\ Init
  /\ [][Next]_counter
  /\ WF_counter(Next)  \*  \A n,m \in Node: WF_counter(Gossip(n,m))

--------------------------------

Constraint ==
  \A n, o \in Node : counter[n][o] <= 2

\* View ==
\*   [
\*     n \in Node |-> [
\*         o \in Node |-> counter[n][o] - Transpose(counter)
\*     ]
\*   ]

--------------------------------

IncrementHardCode(n) ==
  /\ counter[n][n] < 2   \* Hardcoded state constraint
  /\ counter' = [counter EXCEPT ![n][n] = @ + 1]

--------------------------------

Reduction ==
    counter' = [
        n \in Node |-> [
            o \in Node |-> counter[n][o] - Transpose(counter)
        ]
    ]

IncremetAndReduction(n) ==
    Increment(n) \cdot Reduction

GossipAndReduction(n, o) ==
    Gossip(n, o) \cdot Reduction

ReductionNext ==
    \/ \E n \in Node : Increment(n)
    \/ \E n, o \in Node : Gossip(n, o)
    \/ \E n \in Node : IncremetAndReduction(n)
    \/ \E n, o \in Node : GossipAndReduction(n, o)

==============================
------ CONFIG Github1045 -----
SPECIFICATION Spec
PROPERTY Convergence
CONSTANT Node = {n1,n2}
CONSTANT Next <- ReductionNext
CONSTRAINT Constraint
==============================