--------------- MODULE test11 -------------

(* Test of DOMAIN and Function Sets *)

EXTENDS Integers, TLC, FiniteSets


VARIABLE x
Type == x \in BOOLEAN
Init == x = TRUE
Next == UNCHANGED x

f1[i \in Int] == i+3

S == [1..4 -> Nat]

Inv  ==  
  /\ IF 5 \notin DOMAIN f1
       THEN Assert(FALSE, "Test 1 Failed")
       ELSE Print("Test 1 OK", TRUE)

  /\ IF 5 \notin DOMAIN [i \in Int |-> i+3]
       THEN Assert(FALSE, "Test 2 Failed")
       ELSE Print("Test 2 OK", TRUE)

  /\ IF {1,2,3} \notin DOMAIN [T \in SUBSET Int |-> T \cup {1}]
       THEN Assert(FALSE, "Test 3 Failed")
       ELSE Print("Test 3 OK", TRUE)

  /\ IF Cardinality(DOMAIN [i \in {1,3,5} |-> i+7]) # 3
       THEN Assert(FALSE, "Test 4 Failed")
       ELSE Print("Test 4 OK", TRUE)

  /\ IF Cardinality(DOMAIN [f \in [{1,3,5} -> {1,2}] |-> f[3]]) # 8
       THEN Assert(FALSE, "Test 5 Failed")
       ELSE Print("Test 5 OK", TRUE)

  /\ IF Cardinality(DOMAIN [f \in {g \in [{1,3,5} -> {1,2}] : g[3]=1} 
                              |-> f[3]]) # 4
       THEN Assert(FALSE, "Test 6 Failed")
       ELSE Print("Test 6 OK", TRUE)

  /\ IF [i \in {1,3, 5} |-> i-2] \notin 
            {g \in [{1,3,5} -> -2..3] : g[3]=1}
       THEN Assert(FALSE, "Test 7 Failed")
       ELSE Print("Test 7 OK", TRUE)

  /\ IF ~ ((DOMAIN [a |-> 1, b |-> 2]) \subseteq {"a", "b", "cde"})
       THEN Assert(FALSE, "Test 8 Failed")
       ELSE Print("Test 8 OK", TRUE)

  /\ IF <<1, 2, 3, 4>> \notin S
       THEN Assert(FALSE, "Test 9 Failed")
       ELSE Print("Test 9 OK", TRUE)

  /\ IF <<1, 2, -3, 4>> \in S
       THEN Assert(FALSE, "Test 10 Failed")
       ELSE Print("Test 10 OK", TRUE)

  /\ IF <<1, 2, 4>> \in S
       THEN Assert(FALSE, "Test 11 Failed")
       ELSE Print("Test 11 OK", TRUE)

  /\ IF [i \in {1, 2} |-> i] \in S
       THEN Assert(FALSE, "Test 12 Failed")
       ELSE Print("Test 12 OK", TRUE)

  /\ IF [i \in {1, 2, 3, 4} |-> i+1] \notin S
       THEN Assert(FALSE, "Test 13 Failed")
       ELSE Print("Test 13 OK", TRUE)

  /\ IF [i \in {1, 2, 3, 4} |-> i-2] \in S
       THEN Assert(FALSE, "Test 14 Failed")
       ELSE Print("Test 14 OK", TRUE)

  /\ IF [i \in 1..100 |-> i+1]    \notin [1..100 -> Nat]
       THEN Assert(FALSE, "Test 15 Failed")
       ELSE Print("Test 15 OK", TRUE)

  /\ IF [i \in 1..10  |-> i+1]    \in [1..100 -> Nat]
       THEN Assert(FALSE, "Test 16 Failed")
       ELSE Print("Test 16 OK", TRUE)

  /\ IF [i \in {99, 100} |-> i+1] \in [1..100 -> Nat]
       THEN Assert(FALSE, "Test 17 Failed")
       ELSE Print("Test 17 OK", TRUE)

  /\ IF [i \in {"a", "b"} |-> i]  \in [1..100 -> Nat]
       THEN Assert(FALSE, "Test 18 Failed")
       ELSE Print("Test 18 OK", TRUE)

  /\ IF [a |-> 1, b |-> 2]        \in [1..100 -> Nat]
       THEN Assert(FALSE, "Test 19 Failed")
       ELSE Print("Test 19 OK", TRUE)

  /\ Print("Test 20: Enumeration of [{1+1,2} -> {3-1,2,1+1}]", TRUE)
  /\ \A f \in [{1+1,2} -> {3-1,2,1+1}] : Print(f, TRUE)

  /\ Print(<<"Test 21: evaluation of [{1+1,2} -> {3-1,2,1+1}] = ", 
                [{1+1,2} -> {3-1,2,1+1}]>>, TRUE)

  /\ IF /\ Cardinality ([0..1 -> 1..2000]) = 4000000
        /\ Cardinality (1..8099) = 8099
       THEN Print("Test 22 OK", TRUE)
       ELSE Assert(FALSE, "Test 22 Failed")

  /\ IF DOMAIN [i \in {1,2}, j \in {3,4} |-> i+j] # {1,2} \X {3, 4}
       THEN Assert(FALSE, "Test 23 Failed")
       ELSE Print("Test 23 OK", TRUE)

  /\ IF DOMAIN [i \in {1,2}, j \in {3,4}, k \in {5,6} |-> i+j+k] 
                    # {1,2} \X {3, 4} \X {5, 6}
       THEN Assert(FALSE, "Test 24 Failed")
       ELSE Print("Test 24 OK", TRUE)

  /\ IF <<1,3,5>> \notin 
           DOMAIN [i \in {1,2}, j \in {3,4}, k \in {5,6} |-> i+j+k] 
       THEN Assert(FALSE, "Test 25 Failed")
       ELSE Print("Test 25 OK", TRUE)
=========================================
