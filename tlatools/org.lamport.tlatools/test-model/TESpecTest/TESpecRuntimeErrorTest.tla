---------- MODULE TESpecRuntimeErrorTest -----------

EXTENDS Naturals

VARIABLE x

Init == x = [val |-> 0]

Next ==
    \/  /\ x.val < 3
        /\ x' = [val |-> x.val + 1]
    \/  /\ x.val >= 3
        /\ x' = [val2 |-> x.val + 1]

Spec ==
    /\ Init
    /\ [][Next]_<<x>>

==============================================
