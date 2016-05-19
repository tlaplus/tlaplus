--------------- MODULE test50 -------------

(* test usability of the following aliases with the standard modules:
   <=  and >=  of Naturals
   \circ of Sequences
   (+) and (-) of Bags 

*)


EXTENDS Naturals, Sequences, Bags, TLC

Bag1 == SetToBag({"a", "b"})
Bag2 == Bag1 \oplus  SetToBag({"a"}) \* causes TLC bug
Bag3 == Bag2 \ominus Bag1
Bag2a == Bag1 (+) SetToBag({"a"})
Bag3a == Bag2 (-) Bag1


VARIABLES x
Init == x = 0
Next == x'=x

Inv == 
       /\ IF Bag2 = Bag2a
            THEN Print("Test 1 OK", TRUE)
            ELSE Assert(FALSE, "Test 1 Failed") 

       /\ IF Bag3 = Bag3a
            THEN Print("Test 2 OK", TRUE)
            ELSE Assert(FALSE, "Test 2 Failed") 

       /\ IF <<"a">> \o <<"b">> = <<"a">> \circ <<"b">>
            THEN Print("Test 3 OK", TRUE)
            ELSE Assert(FALSE, "Test 3 Failed")  
    
       /\ IF 1 \leq 2
            THEN Print("Test 4 OK", TRUE)
            ELSE Assert(FALSE, "Test 4  Failed") 

       /\ IF 1 <= 2
            THEN Print("Test 5 OK", TRUE)
            ELSE Assert(FALSE, "Test 5  Failed") 
    
       /\ IF 2 \geq 1 
            THEN Print("Test 6 OK", TRUE)
            ELSE Assert(FALSE, "Test 6  Failed") 

       /\ IF 2 >= 1 
            THEN Print("Test 7 OK", TRUE)
            ELSE Assert(FALSE, "Test 7  Failed") 

=======================================
