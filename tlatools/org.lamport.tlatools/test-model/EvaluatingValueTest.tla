------------------------ MODULE EvaluatingValueTest ------------------------
EXTENDS Naturals

VARIABLES x

Init == x = 1

A == x' = FALSE \* This action is replaced by the @Evaluation in EvaluatingValueTest.java

Spec == (x = 1) /\ [][A]_x

Inv == x \in Nat

THEOREM Spec => []Inv

Prop == <>(x = 42)

============================================================================
