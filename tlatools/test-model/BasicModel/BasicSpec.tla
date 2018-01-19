---------------------------- MODULE BasicSpec -----------------------------------
EXTENDS Naturals, FiniteSets

VARIABLE varA, varB
Max == 5

Init == varA = 0 /\ varB = 0

IncA == (varA' = (varA+1) % Max) /\ UNCHANGED varB
IncB == (varB' = (varB+1) % Max) /\ UNCHANGED varA
IncAB == (varA' = (varA+1) % Max) /\ (varB' = (varB+1) % Max)
DecAB == (varA' = (varA-1) % Max) /\ (varB' = (varB-1) % Max)

Next == \/ IncA 
        \/ IncB 
        \/ IncAB
        \/ DecAB

================================================================================
