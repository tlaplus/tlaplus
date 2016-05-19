--------------- MODULE test9 -------------

(* Test of set constructors {x \in S : P(x)} and {e(x) : x \in S} *)

EXTENDS Integers, TLC, FiniteSets

VARIABLE x
Type == x \in BOOLEAN
Init == x = TRUE
Next == UNCHANGED x

Inv  ==  

  /\ IF {i \in {1,3,3,3,4} : i > 1} # {4,3}
       THEN Assert(FALSE, "Test 1 Failed")
       ELSE Print("Test 1 OK", TRUE)

  /\ IF {<<i, j>> \in {1,2} \X {2,3} : j > i} # {<<1,2>>, <<1,3>>, <<2,3>>}
       THEN Assert(FALSE, "Test 2 Failed")
       ELSE Print("Test 2 OK", TRUE)

  /\ IF 2 \notin {i \in Int : i > 1}
       THEN Assert(FALSE, "Test 3 Failed")
       ELSE Print("Test 3 OK", TRUE)

  /\ IF <<3,4>> \notin {<<i,j>> \in Int \X Int : j > i}
       THEN Assert(FALSE, "Test 4 Failed")
       ELSE Print("Test 4 OK", TRUE)

  /\ IF {i+j+k+l+m  : i, j \in {1, 2, 3}, 
                      <<k, l>> \in {4,5} \X {6,7}, m \in {8}} # 20..26
       THEN Assert(FALSE, "Test 5 Failed")
       ELSE Print("Test 5 OK", TRUE)

  /\ IF 24 \notin {i+j+k+l+m  : i, j \in {1, 2, 3}, 
                                <<k, l>> \in {4,5} \X {6,7}, m \in {8}} 
       THEN Assert(FALSE, "Test 6 Failed")
       ELSE Print("Test 6 OK", TRUE)

  /\ IF {i+j : i \in {1,2,3}, j \in {}} # {}
       THEN Assert(FALSE, "Test 7 Failed")
       ELSE Print("Test 7 OK", TRUE)

  /\ IF {i \in {} : i > 2} # {}
       THEN Assert(FALSE, "Test 8 Failed")
       ELSE Print("Test 8 OK", TRUE)

  /\ IF {<<i, j>>  \in {1,3} \X {} : i > 2} # {}
       THEN Assert(FALSE, "Test 9 Failed")
       ELSE Print("Test 9 OK", TRUE)

  /\ IF <<1,2>> \notin {f \in UNION {[S -> {1,2,3}] : 
                          S \in SUBSET {1,2,3}} : f[2] = 2}
       THEN Assert(FALSE, "Test 10 Failed")
       ELSE Print("Test 10 OK", TRUE)

  /\ IF Cardinality({f \in [{1,2,3} -> {1,2,3}] : f[2] > 1}) # 18
       THEN Assert(FALSE, "Test 11 Failed")
       ELSE Print("Test 11 OK", TRUE)

  /\ IF Cardinality([{1,2,3} -> {1,2,3,4}]) # 64
       THEN Assert(FALSE, "Test 12 Failed")
       ELSE Print("Test 12 OK", TRUE)

  /\ IF Cardinality([ {5, 5, 5, 3, 5, 2} -> {1, 3, 3, 3} ]) # 8
       THEN Assert(FALSE, "Test 13 Failed")
       ELSE Print("Test 13 OK", TRUE)

  /\ IF [ {5, 5, 5, 3, 5, 2} -> {1, 3, 3, 3} ] # [{2,3,5} -> {1,3}]
       THEN Assert(FALSE, "Test 14 Failed")
       ELSE Print("Test 14 OK", TRUE)

=========================================
