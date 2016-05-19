--------------- MODULE test12 -------------

(* Test of Record constructs. *)

EXTENDS Integers, TLC, FiniteSets


VARIABLE x
Type == x \in BOOLEAN
Init == x = TRUE
Next == UNCHANGED x


Inv  ==  
LET r1 == [l1 |-> 1, l2 |-> 2, l3 |-> 3]
   r2 == [l1 |-> r1, l2 |-> [r1 EXCEPT !.l2 = 22], l3 |-> [r1 EXCEPT !.l3 = 33]]
   r3 == [l1 |-> [i \in Int |-> i+1], 
          l2 |-> [i , j \in Int |-> [m1 |->i+2, m2 |-> j+3]]]
   
   r4 == [a |-> [i \in 1..1 |-> i],
          b |-> [i \in 1..1 |-> 2]]

   S1 == [l1 : Int, l2 : [{1,2} -> {i \in Int : i > 5}]]
   S2(j) == [l1 : {1,3}, l2 : {f \in [{1,2} -> 1..10] : f[1] > j /\ f[2] > j}]
   S3 == [l1 : Int, l2 : SUBSET [{1,2} -> {2,3}]]

IN
  /\ IF r1.l1 # 1 \/ r1.l1 # 1
       THEN Assert(FALSE, "Test 1 Failed")
       ELSE Print("Test 1 OK", TRUE)

  /\ IF r1["l1"] # 1 \/ r1["l1"] # 1
       THEN Assert(FALSE, "Test 2 Failed")
       ELSE Print("Test 2 OK", TRUE)

  /\ IF [l1 |-> 1, l2 |-> 2, l3 |-> 3].l1 # 1
       THEN Assert(FALSE, "Test 3 Failed")
       ELSE Print("Test 3 OK", TRUE)

  /\ IF [l1 |-> 1, l2 |-> 2, l3 |-> 3]["l1"] # 1
       THEN Assert(FALSE, "Test 4 Failed")
       ELSE Print("Test 4 OK", TRUE)

  /\ IF [1l |-> 1, 2l |-> 2, 3l |-> 3]["2l"] # 2
       THEN Assert(FALSE, "Test 5 Failed")
       ELSE Print("Test 5 OK", TRUE)

  /\ IF r2.l1 # r1 \/ r2.l1 # r1
       THEN Assert(FALSE, "Test 6 Failed")
       ELSE Print("Test 6 OK", TRUE)

  /\ IF r2.l2.l2 # 22 \/ r2.l2.l2 # 22
       THEN Assert(FALSE, "Test 7 Failed")
       ELSE Print("Test 7 OK", TRUE)

  /\ IF r2.l2.l1 # 1 \/ r2.l2.l1 # 1
       THEN Assert(FALSE, "Test 8 Failed")
       ELSE Print("Test 8 OK", TRUE)

  /\ IF [r2 EXCEPT !.l2.l1 = 44, !.l2.l3=55].l2.l1 # 44
       THEN Assert(FALSE, "Test 9 Failed")
       ELSE Print("Test 9 OK", TRUE)

  /\ IF [r2 EXCEPT !.l2.l1 = 44, !.l2.l3=55].l2.l2 # 22
       THEN Assert(FALSE, "Test 10 Failed")
       ELSE Print("Test 10 OK", TRUE)

  /\ IF r3.l2[5,6].m1 # 7 \/ r3.l2[5,6].m1 # 7
       THEN Assert(FALSE, "Test 11 Failed")
       ELSE Print("Test 11 OK", TRUE)

  /\ IF [i , j \in Int |-> [m1 |->i+2, m2 |-> j+3]][5,6].m2 # 9
       THEN Assert(FALSE, "Test 12 Failed")
       ELSE Print("Test 12 OK", TRUE)

  /\ IF r3.l2[5,6].m2 # 9 \/ r3.l2[5,6].m2 # 9
       THEN Assert(FALSE, "Test 14 Failed")
       ELSE Print("Test 13 OK", TRUE)

  /\ IF [l1 |-> 1, l2 |-> [i \in {1,2} |-> i+5]] \notin S1
       THEN Assert(FALSE, "Test 14 Failed")
       ELSE Print("Test 14 OK", TRUE)

  /\ IF [l1 |-> 1, l2 |-> [i \in {1,2} |-> i+4]] \in S1
       THEN Assert(FALSE, "Test 15 Failed")
       ELSE Print("Test 15 OK", TRUE)

  /\ IF ~(S2(5) \subseteq S1) \/ ~(S2(5) \subseteq S1)
       THEN Assert(FALSE, "Test 16 Failed")
       ELSE Print("Test 16 OK", TRUE)

  /\ IF S2(4) \subseteq S1 \/ S2(4) \subseteq S1
       THEN Assert(FALSE, "Test 17 Failed")
       ELSE Print("Test 17 OK", TRUE)
  /\ IF Cardinality(S2(5)) # 50 \/ Cardinality(S2(5)) # 50
       THEN Assert(FALSE, "Test 18 Failed")
       ELSE Print("Test 18 OK", TRUE)

  /\ IF Cardinality([l1 : {1,2}, 
                     l2 : {1, 2, 3, 4, 4, 4, 4}, l3 : {3, 3, 2, 1}]) # 24
       THEN Assert(FALSE, "Test 19 Failed")
       ELSE Print("Test 19 OK", TRUE)

  /\ IF ~(\A r \in S2(5) : r.l2[1] > 5) \/ ~(\A r \in S2(5) : r.l2[1] > 5)
       THEN Assert(FALSE, "Test 20 Failed")
       ELSE Print("Test 20 OK", TRUE)

  /\ IF [l1 |-> -4, l2 |-> {<<3,2>>}] \notin S3
       THEN Assert(FALSE, "Test 21 Failed")
       ELSE Print("Test 21 OK", TRUE)

  /\ IF [l1 |-> -4, l2 |-> {<<3,4>>}] \in S3
       THEN Assert(FALSE, "Test 22 Failed")
       ELSE Print("Test 22 OK", TRUE)

  /\ IF [r4 EXCEPT !["a"][1] = 2]["a"][1] # 2
       THEN Assert(FALSE, "Test 23 Failed")
       ELSE Print("Test 23 OK", TRUE)

=========================================
