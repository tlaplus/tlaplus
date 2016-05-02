--------------------------- MODULE April29 ---------------------------
CONSTANT S

(* Function to choose the other element from the two-element set S *)
Other(n) == CHOOSE x \in S \ {n} : TRUE

VARIABLES x,y
vars == <<x,y>>

Init == x \in S /\ y = 0

NextA == /\ y = 0
         /\ y' = 1
         /\ x' = x

NextB == /\ y = 1
         /\ y' = 1
         /\ x' = x
Spec == Init /\ [][NextA \/ NextB]_vars /\ WF_vars(NextA \/ NextB)

NextC == /\ y = 1
         /\ y' = 1
         /\ x' = Other(x)
SpecD == Init /\ [][NextA \/ NextB \/ NextC]_vars /\ WF_vars(NextA \/ NextB \/ NextC)

=============================================================================
