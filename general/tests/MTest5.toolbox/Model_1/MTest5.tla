------------------------------- MODULE MTest5 ------------------------------- 

(* Generate TLC error when evaluating next-state relation.
Model 1: Evaluation error in Next
Model 1a: Evaluation error in Next
Model 2: Evaluation error in invariant
Model 3: Evaluation error in property.
Model 4: Too many states.
Model 5: Variable value unspecified.
Model 6: Invariant false.
Model 7: Property false.
*)
EXTENDS Naturals
VARIABLE x, y
Init == x=0 /\ y=0
Next == x'=x /\ y'=1-y
Next1a == \/ /\ x = 0
             /\ x'=1
             /\ y'=y
          \/ /\ x = 1
             /\ x'=2
             /\ y'=y \div 0
Next4 == \/ /\ x = 0
            /\ x'=1
            /\ y'=y
         \/ /\ x = 1
            /\ x'=2
            /\ y' \in [1..10 -> 1..4]
             
Next5 ==  \/ /\ x = 0
             /\ x'=1
             /\ y'=y
          \/ /\ x = 1
             /\ x'=2
         
=============================================================================
