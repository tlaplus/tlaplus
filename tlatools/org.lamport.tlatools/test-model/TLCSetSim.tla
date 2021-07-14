--------------------------- MODULE TLCSetSim ---------------------------
EXTENDS Integers, TLC

ASSUME /\ TLCGet("config").depth = 4224
       /\ TLCGet("config").mode \in {"simulate", "generate"}

VARIABLES x

Init == /\ x = 0
        /\ TLCGet("stats").duration >= 0
        /\ TLCGet("stats").traces = 0
        /\ TLCGet("stats").generated = 0

Next == /\ x' = x + 1
        /\ TLCGet("stats").duration >= 0
        /\ TLCGet("stats").traces = 1
        /\ TLCGet("stats").generated = x'
        /\ TLCSet("exit", x = 4223)

Spec == Init /\ [][Next]_x
=============================================================================
