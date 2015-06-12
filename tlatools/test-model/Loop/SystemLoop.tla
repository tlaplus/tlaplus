----------------------------- MODULE SystemLoop -----------------------------

(* System LOOP as described by Manna & Pneuli on page 423ff *)

VARIABLES x
vars == <<x>>

Init == x = 0

One == x = 0 /\ x' = 1
Two == x = 1 /\ x' = 2
Three == x = 2 /\ x' = 3
Back == x = 3 /\ x' = 0

Next == One \/ Two \/ Three \/ Back

Spec == Init /\ [][Next]_vars

SpecWeakFair == Spec /\ WF_vars(Next)

Liveness == []<>(x=3)

=============================================================================
