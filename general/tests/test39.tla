--------------- MODULE test39 -------------

(* Test priming and operator arguments *)

EXTENDS TLC, Integers, Sequences, FiniteSets

VARIABLE x, y

Init == /\ x = [i \in {1,2} |-> i]
        /\ y = 1

Action1(c,d) == c' = [c EXCEPT ![1] = d']
Action2(c,d) == c' = [c EXCEPT ![1] = d]


Next ==  \/ /\ y = 1
            /\ y' = 2
            /\ Action1(x, y)
            /\ IF x[1]' = 2
                 THEN Print("Test1 OK", TRUE)
                 ELSE Assert(FALSE, "Test1 Failed") 

         \/ /\ y = 1
            /\ y' = 2
            /\ Action2(x, y)
            /\ IF x[1]' = 1
                 THEN Print("Test2 OK", TRUE)
                 ELSE Assert(FALSE, "Test2 Failed")

         \/ UNCHANGED <<x, y>>

Inv ==  TRUE
         

Constraint == TRUE
=========================================
