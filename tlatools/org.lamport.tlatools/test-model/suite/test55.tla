------------------------------- MODULE test55 -------------------------------
\* Test of ENABLED with INSTANCE semantics
EXTENDS Naturals

VARIABLE z

I == INSTANCE test55a WITH x <- z, y <- z

Init == z = 0
Next == z' = 1 - z

Spec == Init /\ [][Next]_z /\ WF_z(Next)
Invariant == /\ I!F
             /\ ~I!G

InitProperty == I!Init 
SafeProperty == I!SafeSpec
LiveProperty == I!LiveSpec

=============================================================================


