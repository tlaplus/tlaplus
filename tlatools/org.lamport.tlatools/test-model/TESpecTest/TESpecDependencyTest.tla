---------- MODULE TESpecDependencyTest -----------

EXTENDS Naturals, DoesNotExist

VARIABLE x

Init == x = 0

Next ==
    \/  /\ x < 3
        /\ x' = x + 1
    \/  /\ x >= 3
        /\ UNCHANGED x

Spec ==
    /\ Init
    /\ [][Next]_<<x>>

==============================================
