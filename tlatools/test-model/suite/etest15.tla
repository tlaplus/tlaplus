----------------------  MODULE etest15 -----------------------------
\* Test that TLC distinguishes <<x>> from x in function expressions.

EXTENDS Naturals

S == {<<y>> : y \in {1, 2, 3, 4}}

ASSUME  [<<y>> \in S |-> y+1][2] = [<<y>> \in S |-> y+1][2] 
  
=====================================================================
