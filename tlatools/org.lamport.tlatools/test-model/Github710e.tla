---- MODULE Github710e ----
EXTENDS Naturals
VARIABLE x

Init == x = 0

Inc == x < 2 /\ x' = x + 1 \* x <= 2 - see git commit msg.
Next == Inc

Spec == Init /\ [][Next]_x

FairSpec == Spec /\ WF_x(Next)

VisitsTwoThenStaysSmall == <>(x = 1 /\ <>(x = 2)) => <>[](x < 2)

Tautology == (x = x) ~> (x = x)
====
