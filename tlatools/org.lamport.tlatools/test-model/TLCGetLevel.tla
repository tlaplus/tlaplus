--------------------------- MODULE TLCGetLevel ----------------------------
EXTENDS Integers, TLC

VARIABLES x, y, yb

ASSUME(TLCGet("level") = 0)

Init ==
   /\ yb = TLCGet("level")
   /\ x = 0
   /\ y = TLCGet("level")

Next == 
   /\ yb' = TLCGet("level")
   /\ x < 3 
   /\ x' = x + 1
   /\ y' = TLCGet("level")

Inv ==
   /\ y = yb

ActionConstraint ==
   /\ Assert(TLCGet("level") + 1 = TLCGet("level")', "Failure action constraint")

Prop == <>[](x = 2) /\ [][y' > y /\ yb' > yb]_<<x, y, yb>>
=============================================================================
