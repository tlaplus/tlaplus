---- MODULE FingerprintExceptionHang ----

EXTENDS Naturals

CONSTANTS
    Nodes

VARIABLES
    node_state

vars == <<node_state>>

LegalSets == {{}}

TypeOK ==
    node_state \in [Nodes -> [set: LegalSets]]

Init ==
    \E initial_members \in LegalSets:
        node_state = [n \in Nodes |-> [set |-> initial_members]]

Next ==
    \E n \in Nodes, new_members \in {1}:
        node_state' = [node_state EXCEPT ![n].set = new_members]

Spec == Init /\ [][Next]_vars

====
