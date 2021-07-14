--------------------------- MODULE TLCSet ---------------------------
EXTENDS Integers, TLC

IsBFS == TLCGet("config").mode \notin {"simulate", "generate"}

ASSUME /\ ~IsBFS => TLCGet("config").depth = 4224

VARIABLES x

Init == /\ x = 0
        /\ TLCGet("duration") >= 0 \* Init might take more than a seconds since startup.
        /\ IF IsBFS
           THEN /\ TLCGet("diameter") = 1
                /\ TLCGet("queue") = 0 \* queue is always empty because spec is a single behavior.
                /\ TLCGet("distinct") = 0
           ELSE /\ TLCGet("diameter") = 0

Next == /\ x' = x + 1
        /\ TLCGet("duration") >= 0 \* Next might evaluate within the first second of model checking.
        /\ TLCSet("exit", x = 4223)
        /\ IF IsBFS
           THEN /\ TLCGet("queue") = 0 \* queue is always empty because spec is a single behavior.
                /\ TLCGet("distinct") = x + 1
                /\ TLCGet("generated") = x + 1
		        /\ TLCGet("diameter") = x + 1 \* As byproduct check that trace is strictly monotonically increasing.
           ELSE TRUE

Spec == Init /\ [][Next]_x
=============================================================================
