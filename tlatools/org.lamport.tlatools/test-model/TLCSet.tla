--------------------------- MODULE TLCSet ---------------------------
EXTENDS Integers, TLC

ASSUME TLCGet("config").mode = "bfs"

ASSUME TLCGet("spec").inits = {[name |-> "Init", location |-> [beginLine |-> 15, beginColumn |-> 9, endLine |-> 26, endColumn |-> 40, module |-> "TLCSet"], coverage |-> [distinct |-> 0, generated |-> 0]]}
                
ASSUME TLCGet("spec").actions = {[name |-> "Next", location |-> [beginLine |-> 28, beginColumn |-> 9, endLine |-> 45, endColumn |-> 41, module |-> "TLCSet"], coverage |-> [distinct |-> 0, generated |-> 0]]}

ASSUME TLCSet("s:counter", 0)
ASSUME TLCSet("s:label", "hello")

VARIABLES x

Init == /\ x = 0
        \* Old world
        /\ TLCGet("duration") >= 0 \* Init might take more than a seconds since startup.
        /\ TLCGet("diameter") = 1
        /\ TLCGet("queue") = 0 \* queue is always empty because spec is a single behavior.
        /\ TLCGet("distinct") = 0
        \* New world
        /\ TLCGet("stats").duration >= 0
        /\ TLCGet("stats").queue = 0
        /\ TLCGet("stats").distinct = 0
        /\ TLCGet("stats").diameter = 1
        /\ TLCGet("stats").generated = 0

Next == /\ x' = x + 1
        /\ TLCSet("exit", x = 4223)
        \* Old world
        /\ TLCGet("duration") >= 0 \* Next might evaluate within the first second of model checking.
        /\ TLCGet("queue") = 0 \* queue is always empty because spec is a single behavior.
        /\ TLCGet("distinct") = x'
        /\ TLCGet("generated") = x'
        /\ TLCGet("diameter") = x' \* As byproduct check that trace is strictly monotonically increasing.
        \* Named registers
        /\ TLCGet("s:counter") = x
        /\ TLCGet("s:label") = "hello"
        /\ TLCSet("s:counter", x')
        \* New world
        /\ TLCGet("stats").duration >= 0
        /\ TLCGet("stats").queue = 0
        /\ TLCGet("stats").distinct = x' 
        /\ TLCGet("stats").diameter = x'
        /\ TLCGet("stats").generated = x'

Spec == Init /\ [][Next]_x

PostCondition ==
    /\ TLCGet("s:label") = "hello"
    /\ TLCGet("s:counter") \in Nat

ASSUME TLCGet("config").deadlock = FALSE
ASSUME TLCGet("config").worker = 1
ASSUME TLCGet("config").fingerprint \in STRING
ASSUME TLCGet("config").seed \in STRING

ASSUME TLCGet("spec").temporals = {}
ASSUME TLCGet("spec").invariants = {}
ASSUME TLCGet("spec").impliedinits = {}
ASSUME TLCGet("spec").impliedtemporals = {}

ASSUME TLCGet("revision").tag \in STRING
ASSUME TLCGet("revision").count \in Nat
ASSUME TLCGet("revision").timestamp \in Nat
ASSUME TLCGet("revision").date \in STRING
ASSUME TLCGet("revision").calver \in STRING
ASSUME TLCGet("revision").calver # ""
ASSUME TLCGet("revision").tag = "development" => TLCGet("revision").count = 0 
ASSUME TLCGet("revision").tag # "development" => TLCGet("revision").count > 7854
ASSUME TLCGet("revision").tag # "development" => TLCGet("revision").timestamp > 1626748578
=============================================================================
