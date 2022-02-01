---- MODULE Github710b ----
EXTENDS Naturals

VARIABLE x
vars == <<x>>

Init == x = 1

Next == x' = x + 1

Spec == 
    /\ Init
    /\ [][Next]_vars
    \* /\ WF_x(Next)

StateConstraint ==
    x < 5

AtMostOnce == [](x > 1 => [](x > 2)) \* violated by x = 2
====
