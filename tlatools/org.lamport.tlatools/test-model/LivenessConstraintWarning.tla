----------------------------- MODULE LivenessConstraintWarning -----------------------------
EXTENDS Integers, Sequences

VARIABLES pc, history
vars == <<pc, history>>

Init == /\ pc = "A" 
        /\ history = <<>>

A == /\ pc  = "A"
     /\ pc' = "B"
     /\ history' = history \o <<pc>>

B == /\ pc  = "B"
     /\ pc' = "A"
     /\ UNCHANGED history 

Spec == Init /\ [][A \/ B]_vars /\ WF_vars(A \/ B)

Constraint == Len(history) < 3

Prop == <>(pc = "Done")

==============================================================================
