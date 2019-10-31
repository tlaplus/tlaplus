---- MODULE Github361 ----
EXTENDS TLC, Naturals

Nodes == {1, 2, 3, 4, 5}
null == 6 \* not in Nodes

Vertices == [nodes : SUBSET Nodes, succ : Nodes \cup {null}, dead : BOOLEAN]

Partitions == {P \in SUBSET Vertices :
                 /\ \A v1, v2 \in P : 
                       (v1 # v2) => ((v1.nodes \cap v2.nodes) = {})
                 /\ \A v \in P : /\ v.nodes # {}
                                 /\ \E w \in P : \/ v.succ = null
                                                 \/ v.succ \in w.nodes}     

VARIABLES partition

TypeOK == partition \in Partitions

Init == partition = {}

Next == UNCHANGED partition

=============================================================================
