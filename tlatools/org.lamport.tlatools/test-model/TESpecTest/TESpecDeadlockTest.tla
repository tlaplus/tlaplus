---------- MODULE TESpecDeadlockTest -----------

EXTENDS Naturals

VARIABLES x, y

Init ==
    /\ x = 0
    /\ y = FALSE

Next ==
    /\ x <= 3
    /\ x' = x + 1
    /\ y' = ~y

Spec ==
    /\ Init
    /\ [][Next]_<<x, y>>

==============================================
