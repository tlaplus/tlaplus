------------------------- MODULE May09 -------------------------
EXTENDS Integers
CONSTANT S

VARIABLES x,y
vars == <<x,y>>

Init == x \in S /\ y = 0

NextA == /\ y = 0
         /\ y' = 1
         /\ x' = x

NextB == /\ y >= 1
         /\ y < 5
         /\ y' = y + 1
         /\ x' = x
         
NextC == /\ y = 5
         /\ y' = 1
         /\ x' = x
Spec == Init /\ [][NextA \/ NextB \/ NextC]_vars /\ WF_vars(NextA \/ NextB \/ NextC)

NextD == /\ y = 5
         /\ y' = 1
         /\ \E i \in (S \ {x}) : x' = i
SpecD == Init /\ [][NextA \/ NextB \/ NextD]_vars /\ WF_vars(NextA \/ NextB \/ NextD)

=============================================================================
