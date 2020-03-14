--------------- MODULE test13 -------------

(* Test of Tuples and Cartesian products. *)

EXTENDS Integers, TLC, FiniteSets, Sequences


VARIABLE x
Type == x \in BOOLEAN
Init == x = TRUE
Next == UNCHANGED x

Inv  ==  
LET S1 == {1,2,3} \X {"a", "b", "c", "d"}
    S2 == Int \X [{1,2,3} -> {4, 5, 6}]
    S3 == {1,2,3} \X {"a", "b", "c", "d"} \X {4,5}
    S4 == Int \X [{1,2,3} -> {4, 5, 6}] \X Seq(Int)

IN
  /\ IF Cardinality(S1) # 12 \/ Cardinality(S3) # 24
       THEN Assert(FALSE, "Test 1 Failed")
       ELSE Print("Test 1 OK", TRUE)

  /\ IF \/ <<-5, <<4,4,4>> >> \notin S2
        \/ <<-5, <<4,4,4>>, <<-1,-2,-3>> >>  \notin S4
       THEN Assert(FALSE, "Test 2 Failed")
       ELSE Print("Test 2 OK", TRUE)

  /\ IF <<-5, -4>> \notin Int \X Int
       THEN Assert(FALSE, "Test 3 Failed")
       ELSE Print("Test 3 OK", TRUE)

  /\ IF <<-5, <<4,4,3>>>> \in S2
       THEN Assert(FALSE, "Test 4 Failed")
       ELSE Print("Test 4 OK", TRUE)

  /\ IF {<<"a", "b", "c">>[i] : i \in 1..3} 
          # DOMAIN [a |-> 1, b |-> 2, c |-> {}]
       THEN Assert(FALSE, "Test 5 Failed")
       ELSE Print("Test 5 OK", TRUE)

  /\ IF [i \in {1, 2} |-> IF i = 1 THEN "a" ELSE 22] # <<"a", 22>>
       THEN Assert(FALSE, "Test 6 Failed")
       ELSE Print("Test 6 OK", TRUE)

  /\ IF [i \in {1, 2} |-> IF i = 1 THEN "a" ELSE 22] =  <<"a", 23>>
       THEN Assert(FALSE, "Test 7 Failed")
       ELSE Print("Test 7 OK", TRUE)

  /\ IF <<1,2>> \notin Seq(Int)
       THEN Assert(FALSE, "Test 8 Failed")
       ELSE Print("Test 8 OK", TRUE)

  /\ IF <<1,2>> \notin Seq({n \in Int : n < 22})
       THEN Assert(FALSE, "Test 9 Failed")
       ELSE Print("Test 9 OK", TRUE)

  /\ IF <<1,2>> \in Seq({n \in Int : n > 22})
       THEN Assert(FALSE, "Test 9 Failed")
       ELSE Print("Test 9 OK", TRUE)

  /\ IF <<-5, -4, -3>> \notin Int \X Int \X Int
       THEN Assert(FALSE, "Test 10 Failed")
       ELSE Print("Test 10 OK", TRUE)

  /\ IF <<-5, <<4,4,3>>, <<1,-1>> >> \in S4
       THEN Assert(FALSE, "Test 11 Failed")
       ELSE Print("Test 11 OK", TRUE)

 =========================================
