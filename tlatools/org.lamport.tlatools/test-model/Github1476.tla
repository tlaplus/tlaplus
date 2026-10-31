---------------------------- MODULE Github1476 ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS a, b

VARIABLES s, q, f

Init ==
    /\ s = {a, b}
    /\ q = <<1>>
    /\ f = [m \in {a} |-> [n |-> 0]]

Next ==
    /\ q' = Append(q, 2)
    /\ UNCHANGED <<s, f>>

Spec == Init /\ [][Next]_<<s, q, f>>

Inv == Len(q) < 2

==========================================================================
---------------------------- CONFIG Github1476 ----------------------------
CONSTANTS a = a b = b
SPECIFICATION Spec
INVARIANT Inv
==========================================================================
