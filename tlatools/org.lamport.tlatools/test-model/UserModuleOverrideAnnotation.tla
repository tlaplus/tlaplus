--------------------------- MODULE UserModuleOverrideAnnotation -----------------------
EXTENDS Naturals
VARIABLES x

Get == FALSE
Get2 == FALSE

Init == x = Get

Next == x' = Get2

Spec == Init /\ [][Next]_<<x>>

Prop == [](x = TRUE)
=============================================================================
