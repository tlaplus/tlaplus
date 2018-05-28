------------------------------- MODULE test59 ------------------------------- 
EXTENDS Naturals
\* Test of INSTANCE inside LET

VARIABLE y

Next == LET x == y+1
            M == INSTANCE test59a
        IN  y' = (M!xplus1 - 1) % 5

Init == y = 0

Spec == Init /\ [][Next]_y /\ WF_y(Next)

Invariant == y \in 0..4
Liveness == []<>(y = 4)

=============================================================================