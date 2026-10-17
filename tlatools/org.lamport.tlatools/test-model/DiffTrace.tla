---- MODULE DiffTrace ----
VARIABLES a, b, c, d

Init == a = 0 /\ b = 0 /\ c = 0 /\ d = 0

SetA == a = 0 /\ a' = 1 /\ UNCHANGED <<b, c, d>>
SetB == a = 1 /\ b = 0 /\ b' = 1 /\ UNCHANGED <<a, c, d>>
SetC == b = 1 /\ c = 0 /\ c' = 1 /\ UNCHANGED <<a, b, d>>
SetD == c = 1 /\ d = 0 /\ d' = 1 /\ UNCHANGED <<a, b, c>>

Next == SetA \/ SetB \/ SetC \/ SetD

\* Violated by the fifth state.
InvD == d = 0

\* Violated by the third state.
InvB == b = 0

\* Violated by the second state.
InvA == a = 0
====
