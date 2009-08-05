------------------------------- MODULE MTest3 ------------------------------- 

(* Generate errors that TLC finds when evaluating Assumptions.
Model_1: Generates false assumption.
Model_2: Generates assumption with evaluation error.

*)

VARIABLE x
CONSTANT WhichTest
ASSUME \/ /\ WhichTest = 1
          /\ FALSE
       \/ /\ WhichTest = 2
          /\ 2 = "b"
=============================================================================
