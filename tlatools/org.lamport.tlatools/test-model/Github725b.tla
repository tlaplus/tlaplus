---- MODULE Github725b ----
EXTENDS Naturals

VARIABLE outerX

---- MODULE Inner725b ----
    VARIABLE x

    Step == x < 3 /\ x' = x + 1

    Fairness == WF_x(Step)
====

Svc == INSTANCE Inner725b WITH x <- outerX

Init == outerX = 0

Step ==
    \/ Svc!Step
    \/ ~ENABLED Svc!Step /\ UNCHANGED outerX

Spec ==
    /\ Init
    /\ [][Step]_outerX
    /\ Svc!Fairness

Prop == <>(outerX = 3)

====
