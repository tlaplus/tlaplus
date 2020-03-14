--------------- MODULE test32  -------------

(* Test of [A]_e and <<A>>_e *)

EXTENDS TLC, Naturals, Sequences, FiniteSets

VARIABLE x, y

Init == /\ x = 1
        /\ y = 1

Act1 == /\ x' = 1
        /\ y' = 1

Next == \/ /\ UNCHANGED <<x, y>>
           /\ IF [x # x]_<<x,y>>
                THEN Print("Test1 OK", TRUE)
                ELSE Assert(FALSE, "Test 1 Failed") 
           /\ IF <<Act1>>_<<x,y>>
                THEN Assert(FALSE, "Test 2 Failed")
                ELSE Print("Test2 OK", TRUE)

        \/ /\ <<x'= 1 /\ y'=1>>_y
           /\ Assert(FALSE, "Test 3 Failed")

        \/ /\ Print("Test 4 started -- should finish", TRUE)
           /\ [FALSE]_<<x,y>>
           /\ Print("Test 4 completed" , TRUE)

Inv ==  TRUE

=========================================
