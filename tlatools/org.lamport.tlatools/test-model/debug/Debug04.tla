--------------------------------- MODULE Debug04 ---------------------------------
EXTENDS TLC, Naturals \* Needed for debugger watch expressions.

VARIABLES x

Init == x \in {"A", "B", "C"}

A == x' = "A"

B == x' = "B"

C == x' = "C"

Next == IF TLCGet("level") >= 50 THEN FALSE ELSE A \/ B \/ C

Spec == Init /\ [][Next]_x

==================================================================================
--------------------------------- CONFIG Debug04 ---------------------------------
SPECIFICATION Spec
==================================================================================
