---- MODULE Github971e ----
EXTENDS Integers

VARIABLE x, y
vars == <<x, y>>

Init ==
    x = 0 /\ y = "a"

Next ==
    x' \in {0,1} /\ y' \in {"a", "b"}

Spec ==
    Init /\ [][Next]_x /\ WF_x(Next)

LeadsTo ==
    \* lasso shaped counterexample/liveness property
    x = 0 ~> [](x = 1 => [](y = "a")) 
==========================
