----- MODULE TLCSetInit -----
EXTENDS Integers, TLC

VARIABLES x

Init == x = 1 /\ TLCSet(1,"TLCSet works.")
Next == x < 10 /\ x' = x + 1 /\ PrintT(TLCGet(1))

AtFive == x = 5

Step == x' = x + 1

PossibleCounts ==
    LET p == TLCGet("all:named")["s:_possible"][1]
    IN /\ p["AtFive"] = 1
       /\ p["Step"] = 9

=====