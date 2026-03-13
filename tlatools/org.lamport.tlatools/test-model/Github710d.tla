---- MODULE Github710d ----
EXTENDS Naturals
VARIABLE x

Init == x = 0

Step == x < 3 /\ x' = x + 1 \* x <= 3 - see git commit msg.

Spec == Init /\ [][Step]_x

FairSpec == Spec /\ WF_x(Step)

NeverThree == [](x = 1 => [](x # 3))
====
