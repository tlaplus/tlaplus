-------------------- MODULE InitialLivenessEvaluationError --------------------
EXTENDS Naturals

VARIABLE x

Init == x = 0
Next == (x = 0 /\ x' = 1) \/ UNCHANGED x
Spec == Init /\ [][Next]_x

Inv == x = 0

Prop == <>~ENABLED (x' > x)

=============================================================================
