----------------------------- MODULE test36 --------------------------------

(* Test of standard Bags module *)

EXTENDS Naturals, TLC, Sequences, FiniteSets, Bags

Bag1 == SetToBag({"a", "b"})
Bag2 == Bag1 (+) SetToBag({"a"})

VARIABLES x
Init == x = 0
Next == x'=x

Inv ==
       /\ IF IsABag( Bag1 )
            THEN Print("Test 1 OK", TRUE)
            ELSE Assert(FALSE, "Test 1 Failed")

       /\ IF BagToSet(Bag2) = {"a", "b"}
            THEN Print("Test 2 OK", TRUE)
            ELSE Assert(FALSE, "Test 2 Failed")

       /\ IF BagIn("a", Bag2)
            THEN Print("Test 3 OK", TRUE)
            ELSE Assert(FALSE, "Test 3 Failed")

       /\ IF ~BagIn("c", Bag2)
            THEN Print("Test 4 OK", TRUE)
            ELSE Assert(FALSE, "Test 4 Failed")

       /\ IF BagToSet(EmptyBag) = {}
            THEN Print("Test 5 OK", TRUE)
            ELSE Assert(FALSE, "Test 5 Failed")

       /\ IF EmptyBag (+) Bag2 = Bag2
            THEN Print("Test 6 OK", TRUE)
            ELSE Assert(FALSE, "Test 6 Failed")

       /\ IF Bag2 (-) SetToBag({"a"}) = Bag1
            THEN Print("Test 7 OK", TRUE)
            ELSE Assert(FALSE, "Test 7 Failed")             

       /\ IF Bag1 (-) SetToBag({"a"}) = SetToBag({"b"})
            THEN Print("Test 8 OK", TRUE)
            ELSE Assert(FALSE, "Test 8 Failed")            

       /\ IF BagUnion({Bag1, Bag2}) = Bag1 (+) Bag2
            THEN Print("Test 9 OK", TRUE)
            ELSE Assert(FALSE, "Test 9 Failed")         

       /\ IF Bag1 \sqsubseteq Bag2
            THEN Print("Test 10 OK", TRUE)
            ELSE Assert(FALSE, "Test 10 Failed")   

       /\ Print("TLC Fails Tests 11 & 12 because SubBag not implemented", TRUE)
(*       /\ IF Bag1 \in SubBag(Bag2)
            THEN Print("Test 11 OK", TRUE)
            ELSE Assert(FALSE, "Test 11 Failed")

       /\ IF Cardinality(SubBag(Bag2)) = 6
            THEN Print("Test 12 OK", TRUE)
            ELSE Assert(FALSE, "Test 12 Failed")  *)

       /\ IF LET f(a) == <<"c", a>>
             IN  CopiesIn(<<"c", "a">>, BagOfAll(f, Bag2)) = 2
            THEN Print("Test 13 OK", TRUE)
            ELSE Assert(FALSE, "Test 13 Failed")  

       /\ IF BagCardinality(Bag2) = 3
            THEN Print("Test 14 OK", TRUE)
            ELSE Assert(FALSE, "Test 14 Failed")

       /\ IF CopiesIn("a", Bag2) = 2
            THEN Print("Test 15 OK", TRUE)
            ELSE Assert(FALSE, "Test 15 Failed")

       /\ IF CopiesIn("c", Bag2) = 0
            THEN Print("Test 16 OK", TRUE)
            ELSE Assert(FALSE, "Test 16 Failed")



=============================================================================

(* Last modified on Thu Aug 08 13:28:29 PT 2002 by lamport *)

 6 Apr 99 : Modified version for standard module set
 7 Dec 98 : Corrected error found by Stephan Merz.
 6 Dec 98 : Modified comments based on suggestions by Lyle Ramshaw.
 5 Dec 98 : Initial version.