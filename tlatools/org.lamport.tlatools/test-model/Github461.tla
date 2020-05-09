----------------------------- MODULE Github461 -----------------------------
EXTENDS Integers, TLC

VARIABLES x

Init == x = 0

Next == 
    /\ Assert(x < 4, "Failure of assertion at line 8, column 4.")
    /\ x' = x + 1

====
