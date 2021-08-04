--------------------------- MODULE TLCSetSim ---------------------------
EXTENDS Integers, TLC

ASSUME /\ TLCGet("config").depth = 4224
       /\ TLCGet("config").mode \in {"simulate", "generate"}
       /\ TLCGet("config").traces = -1

ASSUME TLCGet("spec").inits = {[name |-> "Init", location |-> [beginLine |-> 13, beginColumn |-> 9, endLine |-> 16, endColumn |-> 40, module |-> "TLCSetSim"]]}
ASSUME TLCGet("spec").actions = {[name |-> "Next", location |-> [beginLine |-> 18, beginColumn |-> 9, endLine |-> 22, endColumn |-> 35, module |-> "TLCSetSim"]]}

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
    
ASSUME TLCGet("config").deadlock = FALSE
ASSUME TLCGet("config").worker = 1
ASSUME TLCGet("config").aril \in STRING
ASSUME TLCGet("config").seed \in STRING

ASSUME TLCGet("revision").tag \in STRING
ASSUME TLCGet("revision").count \in Nat
ASSUME TLCGet("revision").timestamp \in Nat
ASSUME TLCGet("revision").date \in STRING
ASSUME TLCGet("revision").tag = "development" => TLCGet("revision").count = 0 
ASSUME TLCGet("revision").tag # "development" => TLCGet("revision").count > 7854
ASSUME TLCGet("revision").tag # "development" => TLCGet("revision").timestamp > 1626748578
=============================================================================
