--------------------------- MODULE UserModuleOverrideBase -----------------------
EXTENDS Naturals, UserModuleOverrideFromJar
VARIABLES x

Init == x = Get

Next == x' = Get2

Spec == Init /\ [][Next]_<<x>>

Prop == [](x = TRUE)
=============================================================================
