---- MODULE Github1191 ----
EXTENDS Sequences

Parties == {"A", "B"}
Connections == Parties \X Parties \ {<<x, x>> : x \in Parties}

VARIABLES network, pc

vars == <<network, pc>>

ProcSet == Parties

Init ==
    /\ network = [c \in Connections |-> << >>]
    /\ pc = [self \in ProcSet |-> "Start"]

Start(self) ==
    /\ pc[self] = "Start"
    /\ \E dst \in {p \in Parties : p /= self} :
        network' = [network EXCEPT ![<<self, dst>>] = <<[type |-> "hello"]>>]
    /\ pc' = [pc EXCEPT ![self] = "Done"]

Terminating ==
    /\ \A self \in ProcSet : pc[self] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ \E self \in Parties : Start(self)
    \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Parties : WF_vars(Start(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

=====
----- CONFIG Github1191 -----
SPECIFICATION Spec
PROPERTY Termination
========
