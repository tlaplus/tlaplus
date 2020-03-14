--------------- MODULE test8 -------------

(* Test of set operators \cup, \cap, \subseteq, \ *)

EXTENDS Integers, TLC, Sequences

VARIABLE x
Type == x \in BOOLEAN
Init == x = TRUE
Next == UNCHANGED x

Inv  ==  

  /\ IF {1, 2, 3} \cup {3, 4, 5} # 1..5
       THEN Assert(FALSE, "Test 1 Failed")
       ELSE Print("Test 1 OK", TRUE)

  /\ IF {1, 2, 3} \cap {3, 4, 5} # {3}
       THEN Assert(FALSE, "Test 2 Failed")
       ELSE Print("Test 2 OK", TRUE)

  /\ IF -5 \notin Int \cup Nat 
       THEN Assert(FALSE, "Test 3 Failed")
       ELSE Print("Test 3 OK", TRUE)

  /\ IF -5 \notin Nat \cup Int
       THEN Assert(FALSE, "Test 4 Failed")
       ELSE Print("Test 4 OK", TRUE)

  /\ IF {1, 2, 3, 4} \cap {i \in Int : i > 2} # {3, 4}
       THEN Assert(FALSE, "Test 5 Failed")
       ELSE Print("Test 5 OK", TRUE)

  /\ IF {1, 2, 3} \cap {} # {}
       THEN Assert(FALSE, "Test 6 Failed")
       ELSE Print("Test 6 OK", TRUE)

  /\ IF {} \cap {1, 2, 3} # {}
       THEN Assert(FALSE, "Test 7 Failed")
       ELSE Print("Test 7 OK", TRUE)

  /\ IF {1, 2, 3, 4} \ {i \in Int : i > 2} # {2, 1}
       THEN Assert(FALSE, "Test 8 Failed")
       ELSE Print("Test 8 OK", TRUE)

  /\ IF {1, 2, 3} \ {} # {3,1,2}
       THEN Assert(FALSE, "Test 9 Failed")
       ELSE Print("Test 9 OK", TRUE)

  /\ IF {} \ {1, 2, 3} # {}
       THEN Assert(FALSE, "Test 10 Failed")
       ELSE Print("Test 10 OK", TRUE)

  /\ IF -5 \in {-5} \ Int
       THEN Assert(FALSE, "Test 11 Failed")
       ELSE Print("Test 11 OK", TRUE)

  /\ IF <<1, 2>> \in Seq({1,2,3}) \ Seq({1,2})
       THEN Assert(FALSE, "Test 12 Failed")
       ELSE Print("Test 12 OK", TRUE)

  /\ IF <<1, 2>> \notin Seq({1,2,3}) 
       THEN Assert(FALSE, "Test 12a Failed")
       ELSE Print("Test 12a OK", TRUE)

  /\ IF <<1, 2>> \notin Seq({1,2,3}) \cap  Seq({0,1,2})
       THEN Assert(FALSE, "Test 13 Failed")
       ELSE Print("Test 13 OK", TRUE)

  /\ IF <<1, 2>> \notin Seq({0,1}) \cup  Seq({1,2,3}) 
       THEN Assert(FALSE, "Test 14 Failed")
       ELSE Print("Test 14 OK", TRUE)

  /\ IF <<1, 2>> \in [1..2 ->{1,2,3}] \ [1..2 ->{1,2}]
       THEN Assert(FALSE, "Test 16 Failed")
       ELSE Print("Test 16 OK", TRUE)

  /\ IF <<1, 2>> \notin [1..2 ->{1,2,3}] 
       THEN Assert(FALSE, "Test 17 Failed")
       ELSE Print("Test 17 OK", TRUE)

  /\ IF <<1, 2>> \notin [1..2 ->{1,2,3}] \cap  [1..2 ->{0,1,2}]
       THEN Assert(FALSE, "Test 18 Failed")
       ELSE Print("Test 18 OK", TRUE)

  /\ IF <<1, 2>> \notin [1..2 ->{0,1}] \cup [1..2 ->{1,2,3}] 
       THEN Assert(FALSE, "Test 19 Failed")
       ELSE Print("Test 19 OK", TRUE)

  /\ IF ~({1,2,3} \subseteq Int)
       THEN Assert(FALSE, "Test 20 Failed")
       ELSE Print("Test 20 OK", TRUE)

  /\ IF {1,2,3} \subseteq {i \in Int : i < 3}
       THEN Assert(FALSE, "Test 21 Failed")
       ELSE Print("Test 21 OK", TRUE)

  /\ IF <<1,2>> \in ({1,2} \X Nat) \cup {<<3,4>>, <<5,6>>}
       THEN Print("Test 22 OK", TRUE)
       ELSE Assert(FALSE, "Test 22 Failed")

=========================================
