--------------- MODULE test42 -------------

(* Test of operator arguments  *)

EXTENDS TLC, Integers, Sequences

VARIABLE x

a ++ b == a + b

Foo(a, _--_) == a -- 0


Init == x = 1


Next ==  x' = x
         
FooBar(a, Op(_,_)) == Op(a, 0)

Plus(a, b) == a + b

Inv ==  /\ IF FooBar(7, Plus) = 7
             THEN Print("Test 1 OK", TRUE)
             ELSE Assert(FALSE, "Test 1 Failed")  

        /\ IF FooBar(7,+) = 7 
             THEN Print("Test 2 OK", TRUE)
             ELSE Assert(FALSE, "Test 2 Failed")  

        /\ IF Foo(7, *) = 0 
             THEN Print("Test 3 OK", TRUE)
             ELSE Assert(FALSE, "Test 3 Failed")  

        /\ IF Foo(7,+) = 7 
             THEN Print("Test 4 OK", TRUE)
             ELSE Assert(FALSE, "Test 4 Failed")  

        /\ IF Foo(7,++) = 7 
             THEN Print("Test 5 OK", TRUE)
             ELSE Assert(FALSE, "Test 5 Failed")  

Constraint == TRUE
=========================================
