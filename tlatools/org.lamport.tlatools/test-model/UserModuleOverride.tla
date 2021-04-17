--------------------------- MODULE UserModuleOverride -----------------------
EXTENDS Naturals, TLC
VARIABLES x

Get == FALSE

Get2 == TRUE

Init == x = Get

Next == x' = Get2

Spec == Init /\ [][Next]_<<x>>

Prop == <>[](Print(x, x = TRUE))
=============================================================================
