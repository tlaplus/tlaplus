----- MODULE TLCSetInit -----
EXTENDS Integers, TLC

VARIABLES x

Init == x = 1 /\ TLCSet(1,"TLCSet works.")
Next == x < 10 /\ x' = x + 1 /\ PrintT(TLCGet(1))

=====