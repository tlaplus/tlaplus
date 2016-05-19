--------------- MODULE test1 -------------

(* test equality of various representations of sets.    *)

EXTENDS Naturals, TLC

VARIABLE x


Type == x \in {1}
Inv  == 
 /\ IF {1, 2, 3} # {3, 2, 2, 1}
      THEN Assert(FALSE, "Failed Test 1")
      ELSE Print("Test 1 OK", TRUE)

 /\ IF  {1, 2, 3} # {i \in {5, 4, 3, 2, 1} : i < 4}
      THEN Assert(FALSE, "Failed Test 2")
      ELSE Print("Test 2 OK", TRUE)

 /\ IF {1, 2, 3} # {i-3 : i \in {4, 6, 5, 6, 5, 6}}
      THEN Assert(FALSE, "Failed Test 3")
      ELSE Print("Test 3 OK", TRUE)

 /\ IF SUBSET {1, 2, 3} # {{}, {1}, {2,1,2}, {3,1}, {2}, {3}, {3,2,3}, {1,2,3}}
      THEN Assert(FALSE, "Failed Test 4")
      ELSE Print("Test 4 OK", TRUE)

 /\ IF {1,2,3} # UNION (SUBSET {1, 2, 3})
      THEN Assert(FALSE, "Failed Test 5")
      ELSE Print("Test 5 OK", TRUE)    

 /\ IF {1,2,3} # UNION {{1}, {2}, {3, 2, 1}}
      THEN Assert(FALSE, "Failed Test 6")
      ELSE Print("Test 6 OK", TRUE)

 /\ IF {1,2,3} # {1} \cup {3, 2} \cup {}
      THEN Assert(FALSE, "Failed Test 7")
      ELSE Print("Test 7 OK", TRUE)

 /\ IF {1,2,3} # {5, 4, 3, 2, 1} \cap {1, 3, 0, 2}
      THEN Assert(FALSE, "Failed Test 8")
      ELSE Print("Test 8 OK", TRUE)

 /\ IF {1,2,3} \subseteq {5, 3, 3, 4, 2}
      THEN Assert(FALSE, "Failed Test 9")
      ELSE Print("Test 9 OK", TRUE)

 /\ IF {1,2,3} # {5, 3, 3, 4, 2,1} \ {4, 5}
      THEN Assert(FALSE, "Failed Test 10")
      ELSE Print("Test 10 OK", TRUE)

 /\ IF {1,2,3} # 1..3
      THEN Assert(FALSE, "Failed Test 11")
      ELSE Print("Test 11 OK", TRUE)

 /\ IF {1,2,3} # DOMAIN <<"a", "b", "c">>
      THEN Assert(FALSE, "Failed Test 12")
      ELSE Print("Test 12 OK", TRUE)

 /\ IF {1,2,3} # DOMAIN [i \in {3,2,2,1} |-> i+1]
      THEN Assert(FALSE, "Failed Test 13")
      ELSE Print("Test 13 OK", TRUE)

 /\ IF {"a", "b", "c"} # DOMAIN [a |-> 1, b |-> 2, c |-> 3]
      THEN Assert(FALSE, "Failed Test 14")
      ELSE Print("Test 14 OK", TRUE)

 /\ IF {} # [{1, 2, 3} -> {}]
      THEN Assert(FALSE, "Failed Test 15")
      ELSE Print("Test 15 OK", TRUE)

 /\ Print("Test Completed", TRUE)

Init == x = 1

Next == UNCHANGED x
=========================================
