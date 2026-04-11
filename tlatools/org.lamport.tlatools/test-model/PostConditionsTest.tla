---- MODULE PostConditionsTest ----
EXTENDS Naturals, TLC
VARIABLE x

Init == x = 0

Next == x < 3 /\ x' = x + 1

Spec == Init /\ [][Next]_x

Post1 == TLCSet(100, TLCGet("generated"))

Post2 == TLCSet(101, TLCGet("distinct"))

PostFail == TLCGet("distinct") = 42

AtTwo == x = 2

LastStep == x = 2 /\ x' = 3

PossibleCounts ==
    LET p == TLCGet("all:named")["s:_possible"][1]
    IN /\ p["AtTwo"] = 1
       /\ p["LastStep"] = 1
====
