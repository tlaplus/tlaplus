--------------------------- MODULE UserModuleOverride -----------------------
EXTENDS Naturals
VARIABLES x

Get == FALSE

Init == x = Get

Next == x' = TRUE

Spec == Init /\ [][Next]_<<x>>

Prop == [](x = TRUE)
=============================================================================
