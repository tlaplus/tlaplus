---------------------------- MODULE Github807 ---------------------------
EXTENDS Naturals
VARIABLE x

Init == x = 0

Add(d,n) ==
    /\ x' = x + d
    /\ x' <= 10

Next(r) ==
    LET d == IF x = x THEN 1 ELSE 1
    IN Add(d,r)

IsNotTwo == x # 2

Spec == Init /\ [][Next(1)]_x

==============================================================================
---------------------------- CONFIG Github807 ----------------------------
SPECIFICATION Spec

INVARIANT IsNotTwo
===========================================================================
