------------------------------- MODULE MTest4 ------------------------------- 

(* Generate TLC error when evaluating initial states.
Model 1: Evaluation error in Init
Model 2: Evaluation error in invariant
Model 3: Evaluation error in property.
Model 4: Too many states.
Model 5: Variable value unspecified.
Model 6: Invariant false.
Model 7: Property false.
*)

VARIABLE x, y

=============================================================================
