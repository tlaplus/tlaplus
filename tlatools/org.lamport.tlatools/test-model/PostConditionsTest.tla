---- MODULE PostConditionsTest ----
EXTENDS Naturals, TLC
VARIABLE x

Init == x = 0

Next == x < 3 /\ x' = x + 1

Spec == Init /\ [][Next]_x

Post1 == TLCSet(100, TLCGet("generated"))

Post2 == TLCSet(101, TLCGet("distinct"))

PostFail == TLCGet("distinct") = 42
====
