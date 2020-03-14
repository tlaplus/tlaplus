--------------------------- MODULE TLCSet ---------------------------
EXTENDS Integers, TLC

VARIABLES x

Init == /\ x = 0
        /\ TLCGet("diameter") = 1
        /\ TLCGet("queue") = 0
        /\ TLCGet("distinct") = 0
        /\ TLCGet("duration") >= 0 \* Init might take more than a seconds since startup.

Next == /\ x' = x + 1
        /\ TLCGet("distinct") = x + 1
		/\ TLCGet("diameter") = x + 1 \* As byproduct check that trace is strictly monotonically increasing.
        /\ TLCGet("queue") = 0 \* queue is always empty because spec is a single behavior.
        /\ TLCGet("duration") >= 0 \* Next might evaluate within the first second of model checking.
        /\ TLCSet("exit", x = 4223)

Spec == Init /\ [][Next]_x
=============================================================================
