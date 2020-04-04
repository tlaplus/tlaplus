--------------------------- MODULE TLCGetLevel ----------------------------
EXTENDS Integers, TLC

VARIABLES x, y

ASSUME(TLCGet("level") = 0)

Init == /\ x = 0
        /\ y = TLCGet("level")

Next == /\ x < 3 
        /\ x' = x + 1
        /\ y' = TLCGet("level")
        
Prop == <>[](x = 2)
=============================================================================
