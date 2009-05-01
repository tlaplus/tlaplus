--------------- MODULE test34  -------------

(* Test Model Values *)

EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS a, b, c

VARIABLE x

Init == x = 1

Next == UNCHANGED x

Inv ==  /\ IF a \in STRING THEN Assert(FALSE, "Test 1 failed")
                           ELSE Print("Test 1 OK", TRUE)
        /\ IF a = {1, 2}   THEN Assert(FALSE, "Test 2 failed")
                           ELSE Print("Test 2 OK", TRUE)
        /\ IF a \in {i \in Nat : i > 7} 
             THEN Assert(FALSE, "Test 3 failed")
             ELSE Print("Test 3 OK", TRUE)
        /\ IF a \in {b, c} THEN Assert(FALSE, "Test 4 failed")
                           ELSE Print("Test 4 OK", TRUE)

=========================================
