---------------------------- MODULE Github849 ---------------------------

CONSTANTS
    Nodes

VARIABLES
    n,
    node_set

TypeOK ==
    /\ n = 1

Init ==
    /\ n = 1
    /\ node_set = {}

Next ==
    /\ n' = 2
    /\ node_set' = {v \in SUBSET Nodes : FALSE}

==========================================================================
---------------------------- CONFIG Github849 ----------------------------

INIT Init
NEXT Next

CONSTANT Nodes = {A1}

CHECK_DEADLOCK FALSE
INVARIANT TypeOK

===========================================================================
