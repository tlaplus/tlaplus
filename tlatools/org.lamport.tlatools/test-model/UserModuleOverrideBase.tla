--------------------------- MODULE UserModuleOverrideBase -----------------------
EXTENDS Naturals, UserModuleOverrideFromJar, TLC
VARIABLES x

Init == x = Get

Next == x' = Get2

Spec == Init /\ [][Next]_<<x>>

Prop == <>[](Print(x, x = TRUE))
=============================================================================
