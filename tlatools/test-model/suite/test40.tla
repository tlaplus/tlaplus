------------------------------ MODULE test40 -----------------------------
(* Test of standard Naturals module.    *)

EXTENDS Naturals, TLC

VARIABLES x

Init == x = 0

Next == UNCHANGED x

Inv == 
       /\ IF  2^10 + 2^10 = 2^11
            THEN Print("Test 1 OK", TRUE)
            ELSE Assert(FALSE, "Test 1 Failed")    

       /\ IF 0^20 = 0
            THEN Print("Test 2 OK", TRUE)
            ELSE Assert(FALSE, "Test 2 Failed")    

       /\ IF 2^21 - 2^20 = 2^20
            THEN Print("Test 2a OK", TRUE)
            ELSE Assert(FALSE, "Test 2a Failed") 

       /\ IF 2 - 3 \notin Nat
            THEN Print("Test 3 OK", TRUE)
            ELSE Assert(FALSE, "Test 3 Failed")

       /\ IF 123 * 345 = 42435
            THEN Print("Test 4 OK", TRUE)
            ELSE Assert(FALSE, "Test 4 Failed")

       /\ IF 123 < 124
            THEN Print("Test 5 OK", TRUE)
            ELSE Assert(FALSE, "Test 5 Failed")

       /\ IF 12345 > 12344
            THEN Print("Test 6 OK", TRUE)
            ELSE Assert(FALSE, "Test 6 Failed")

       /\ IF 123 \leq 123
            THEN Print("Test 7 OK", TRUE)
            ELSE Assert(FALSE, "Test 7 Failed")

       /\ IF 12345 \geq 12345
            THEN Print("Test 8 OK", TRUE)
            ELSE Assert(FALSE, "Test 8 Failed")

       /\ IF 123 \leq 124
            THEN Print("Test 9 OK", TRUE)
            ELSE Assert(FALSE, "Test 9 Failed")

       /\ IF 12344 \geq 12333
            THEN Print("Test 10 OK", TRUE)
            ELSE Assert(FALSE, "Test 10 Failed")

       /\ IF 145939 = 487 * (145939 \div 487) + (145939 % 487) 
            THEN Print("Test 11 OK", TRUE)
            ELSE Assert(FALSE, "Test 11 Failed")  

       /\ IF 139982 \div 1 = 139982 
            THEN Print("Test 12 OK", TRUE)
            ELSE Assert(FALSE, "Test 12 Failed")

       /\ IF 123099 % 1 = 0
            THEN Print("Test 13 OK", TRUE)
            ELSE Assert(FALSE, "Test 13 Failed")

       /\ IF 0 % 345 = 0
            THEN Print("Test 14 OK", TRUE)
            ELSE Assert(FALSE, "Test 14 Failed")  

       /\ IF 24 % 9 = 6
            THEN Print("Test 15 OK", TRUE)
            ELSE Assert(FALSE, "Test 15 Failed")   

       /\ IF 4566799 = 423 * (4566799 \div 423) + (4566799 % 423)
            THEN Print("Test 16 OK", TRUE)
            ELSE Assert(FALSE, "Test 16 Failed")    

       /\ IF 2222222 = 18 * (2222222 \div 18) + (2222222 % 18)
            THEN Print("Test 17 OK", TRUE)
            ELSE Assert(FALSE, "Test 17 Failed")   

       /\ IF 3 .. 2 = {}
            THEN Print("Test 18 OK", TRUE)
            ELSE Assert(FALSE, "Test 18 Failed")

       /\ IF 2..4 = {2, 3, 4}
            THEN Print("Test 19 OK", TRUE)
            ELSE Assert(FALSE, "Test 19 Failed")

       /\ IF (0-1) * (0-3) = 3
            THEN Print("Test 20 OK", TRUE)
            ELSE Assert(FALSE, "Test 20 Failed")

       /\ IF (0-1) % 3 = 2
            THEN Print("Test 21 OK", TRUE)
            ELSE Assert(FALSE, "Test 21 Failed")

=============================================================================
