--------------------------- MODULE TLCGetLevel ----------------------------
EXTENDS Integers, TLC

VARIABLES x, y, yb, z

ASSUME(TLCGet("level") = 0)

Init ==
   /\ TLCGet("level") = 0
   /\ yb = TLCGet("level")
   /\ x = 0
   /\ y = TLCGet("level")
   /\ z = 1

Next == 
   /\ TLCGet("level") > 0
   /\ Assert(TLCGet("level") + 1 = TLCGet("level")', "Failure pre next-state")
   /\ yb' = TLCGet("level")
   /\ x < 3 
   /\ x' = x + 1
   /\ y' = TLCGet("level")
   /\ z' = TLCGet("level")'
   /\ Assert(TLCGet("level") + 1 = TLCGet("level")', "Failure post next-state")

Inv ==
    /\ y = yb
    /\ z = TLCGet("level")
    /\ x + 1 = TLCGet("level")
    \* /\ TLCGet("level") < 4  \* To trigger a safety violation.

ActionConstraint ==
    /\ Assert(TLCGet("level") + 1 = TLCGet("level")', "Failure action constraint")

StateConstraint ==
    /\ TLCGet("level") \in 1..4

Prop ==
    /\ <>[](x = 2)
    /\ [][y' > y /\ yb' > yb /\ TLCGet("level") + 1 = TLCGet("level")']_<<x, y, yb, z>>
=============================================================================
