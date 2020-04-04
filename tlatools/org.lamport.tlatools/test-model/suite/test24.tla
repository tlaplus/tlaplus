--------------- MODULE test24 -------------

(* Test of UNCHANGED *)

EXTENDS Naturals, TLC

VARIABLES x, y

Init == /\ x = [i \in 1..3 |-> i]
        /\ y = 1
Next == 

  \/ /\ UNCHANGED <<x, y>>
     /\ \A i \in 1..3 : (x[i])' = x[i]
     /\ Print("Test 1 OK", TRUE)

  \/ /\ UNCHANGED <<x, y>>
     /\ \A i \in 1..3 : UNCHANGED x[i]
     /\ Print("Test 2 OK", TRUE)

  \/ /\ UNCHANGED <<x, y>>
     /\ \A i \in 1..3 : UNCHANGED [a |-> x[i], b |-> x[i]+1]
     /\ Print("Test 3 OK", TRUE)

  \/ /\ UNCHANGED <<x, y>>
     /\ IF UNCHANGED \E i \in 1..3 : x[i]=3
          THEN Print("Test 4 OK", TRUE)
          ELSE Assert(FALSE, "Test 4 Failed")

  \/ /\ UNCHANGED <<x, y>>
     /\ IF UNCHANGED \A i \in 1..3 : x[i]=3
          THEN Print("Test 5 OK", TRUE)
          ELSE Assert(FALSE, "Test 5 Failed")

  \/ /\ UNCHANGED <<x, y>>
     /\ IF UNCHANGED CHOOSE i \in DOMAIN x : x[i] = 2
          THEN Print("Test 6 OK", TRUE)
          ELSE Assert(FALSE, "Test 6 Failed")

  \/ /\ UNCHANGED <<x, y>>
     /\ IF UNCHANGED {x[i] : i \in 1..2}
          THEN Print("Test 7 OK", TRUE)
          ELSE Assert(FALSE, "Test 7 Failed")

  \/ /\ UNCHANGED <<x, y>>
     /\ IF UNCHANGED {i \in 3..5 : \E j \in 1..3 : x[j]=i}
          THEN Print("Test 8 OK", TRUE)
          ELSE Assert(FALSE, "Test 8 Failed")

  \/ /\ UNCHANGED <<x, y>>
     /\ IF UNCHANGED DOMAIN x
          THEN Print("Test 9 OK", TRUE)
          ELSE Assert(FALSE, "Test 9 Failed")

  \/ /\ (y=1) /\ (y' = y+1)
     /\ UNCHANGED <<x>>
     /\ IF UNCHANGED {x}
          THEN Print("Test 10 OK", TRUE)
          ELSE Assert(FALSE, "Test 10 Failed")

  \/ /\ (y=1) /\ (y' = y+1)
     /\ UNCHANGED <<x>>
     /\ IF UNCHANGED {1, 2, y}
          THEN Print("Test 11 OK", TRUE)
          ELSE Assert(FALSE, "Test 11 Failed")

Inv == TRUE
==========================================================================


=============================================================================
