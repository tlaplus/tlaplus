---- MODULE PossibleFailTest ----
EXTENDS Naturals
VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 3

Unreachable == x = 5

BigJump == x' = x + 2

Spec == Init /\ [][Next]_x
====
