-------- MODULE BidirectionalTransitions --------
EXTENDS Naturals
VARIABLE x

-------------------------------------------------

A == \/ x' = (x + 1) % 3
B == x' \in 0..2
Spec1A == (x=0) /\ [][A \/ B]_x/\ WF_x(A)
Prop1A == Spec1A /\ WF_x(A) /\ []<><<A>>_x

Fair1B == WF_x(B)
Spec1B == (x=0) /\ [][A \/ B]_x/\ Fair1B
Prop1Bx == WF_x(A)
Prop1By == []<><<A>>_x

-------------------------------------------------

C == x' = (x + 1) % 4
D == IF x = 0 THEN x' = 3 ELSE  x' = x - 1 
Spec2 == (x=0) /\ [][C \/ D]_x/\ WF_x(D)
Prop2 == Spec2 /\ WF_x(D) /\ []<><<D>>_x

Fair2C == WF_x(C)
Spec2C == (x=0) /\ [][C \/ D]_x/\ Fair2C
Prop2Cx == WF_x(D)
Prop2Cy == []<><<D>>_x
=================================================
