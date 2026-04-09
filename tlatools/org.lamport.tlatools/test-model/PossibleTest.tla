---- MODULE PossibleTest ----
EXTENDS Naturals, TLC
VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 3

AllDone == x = 2

AtOne == x = 1

WrapAround == x = 2 /\ x' = 0

Spec == Init /\ [][Next]_x

PossibleCounts ==
    LET p == TLCGet("all:named")["s:_possible"][1]
    IN /\ p["AllDone"] = 1
       /\ p["AtOne"] = 1
       /\ p["WrapAround"] = 1
====
