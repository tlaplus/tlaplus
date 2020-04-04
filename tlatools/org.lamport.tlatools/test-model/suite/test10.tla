--------------- MODULE test10 -------------

(* Test of function definition and application *)

EXTENDS Integers, TLC

VARIABLE x
Type == x \in BOOLEAN
Init == x = TRUE
Next == UNCHANGED x

f1[i \in Int]  == i+2
f2[i, j \in Int] == i+j
f3[i, j \in Int, <<k,l>> \in Int \X Int, m \in {5, 7,8}] == 
        i + 2*j + 3*k + 4*l + 5*m
f4[i, j \in Int] == [a |-> i, b |-> j]

f5[i, j, k \in Int] == i+j+k

f6[i, j, k \in Int, <<l, m, n>> \in Int \X Int \X Int, p \in {5,7,8}] ==
        i + 2*j + 3*k + 4*l + 5*m + 6*n + 7*p

Inv  ==  

LET r1 == [a |-> f1, b |-> f2]
    g1 == [f4 EXCEPT ![1,2].a = 22, ![1,3].b = 33]
    g2 == [[<<i, j>> \in (1..10) \X (1..10) 
            |-> [a |-> i, b |-> j]] EXCEPT ![1,2].a = 22, ![1,3].b = 33]
IN
  /\ IF f1[3] # 5
       THEN Assert(FALSE, "Test 1 Failed")
       ELSE Print("Test 1 OK", TRUE)

  /\ IF f2[3,4] # 7
       THEN Assert(FALSE, "Test 2 Failed")
       ELSE Print("Test 2 OK", TRUE)

  /\ IF f2[<<3,4>>] # 7
       THEN Assert(FALSE, "Test 3 Failed")
       ELSE Print("Test 3 OK", TRUE)

  /\ IF f3[1, 2, <<3, 4>>, 5] # 55
       THEN Assert(FALSE, "Test 4 Failed")
       ELSE Print("Test 4 OK", TRUE)

  /\ IF f3[<<1, 2, <<3, 4>>, 5>>] # 55
       THEN Assert(FALSE, "Test 5 Failed")
       ELSE Print("Test 5 OK", TRUE)


  /\ IF [i \in Int |-> i+2][3] # 5
       THEN Assert(FALSE, "Test 6 Failed")
       ELSE Print("Test 6 OK", TRUE)

  /\ IF [i, j \in Int |-> i+j][3,4] # 7
       THEN Assert(FALSE, "Test 7 Failed")
       ELSE Print("Test 7 OK", TRUE)

  /\ IF [i, j \in Int |-> i+j][<<3,4>>] # 7
       THEN Assert(FALSE, "Test 8 Failed")
       ELSE Print("Test 8 OK", TRUE)

  /\ IF [i, j \in Int, <<k,l>> \in Int \X Int, m \in {5,7,8} 
         |-> i + 2*j + 3*k + 4*l + 5*m][1, 2, <<3, 4>>, 5] # 55
       THEN Assert(FALSE, "Test 9 Failed")
       ELSE Print("Test 9 OK", TRUE)

  /\ IF [i, j \in Int, <<k,l>> \in Int \X Int, m \in {5,7,8} 
         |-> i + 2*j + 3*k + 4*l + 5*m][<<1, 2, <<3, 4>>, 5>>] # 55
       THEN Assert(FALSE, "Test 10 Failed")
       ELSE Print("Test 10 OK", TRUE)

  /\ IF [f1 EXCEPT ![3] = [i \in Int |-> @ + i]][3][7] # 12
       THEN Assert(FALSE, "Test 11 Failed")
       ELSE Print("Test 11 OK", TRUE)

  /\ IF [f1 EXCEPT ![3] = [i \in Int |-> @ + i],  ![3][6] = 44][3][6] # 44
       THEN Assert(FALSE, "Test 12 Failed")
       ELSE Print("Test 12 OK", TRUE)

  /\ IF [f1 EXCEPT ![3] = [i \in Int |-> @ + i], ![3][6] = 44][3][7] # 12
       THEN Assert(FALSE, "Test 13 Failed")
       ELSE Print("Test 13 OK", TRUE)

  /\ IF f4[3,4].a # 3
       THEN Assert(FALSE, "Test 14 Failed")
       ELSE Print("Test 14 OK", TRUE)

  /\ IF [f4 EXCEPT ![3,4].b = 17][3,4].b # 17
       THEN Assert(FALSE, "Test 15 Failed")
       ELSE Print("Test 15 OK", TRUE)

  /\ IF [f4 EXCEPT ![3,4].b = 17][3,4].a # 3
       THEN Assert(FALSE, "Test 16 Failed")
       ELSE Print("Test 16 OK", TRUE)

  /\ IF [f4 EXCEPT ![3,4].b = 17][2,4].b # 4
       THEN Assert(FALSE, "Test 17 Failed")
       ELSE Print("Test 17 OK", TRUE)

  /\ IF [f4 EXCEPT ![3,4].b = 17, ![3,4].a = 18][3,4].b # 17
       THEN Assert(FALSE, "Test 18 Failed")
       ELSE Print("Test 18 OK", TRUE)

  /\ IF [f4 EXCEPT ![3,4].b = 17, ![3,4].a = 18][3,4].a # 18
       THEN Assert(FALSE, "Test 19 Failed")
       ELSE Print("Test 19 OK", TRUE)

  /\ IF [f4 EXCEPT ![3,4].b = 17, ![3,4].a = 18, ![3,4].b= @+5][3,4].b # 22
       THEN Assert(FALSE, "Test 20 Failed")
       ELSE Print("Test 20 OK", TRUE)

  /\ IF [f4 EXCEPT ![3,4].b = 17, ![3,4].a = 18, ![<<3,4>>].b= @+5][3,4].b # 22
       THEN Assert(FALSE, "Test 21 Failed")
       ELSE Print("Test 21 OK", TRUE)

  /\ IF g1[1,3].a # 1 \/ g1[1,3].a # 1
       THEN Assert(FALSE, "Test 22 Failed")
       ELSE Print("Test 22 OK", TRUE)

  /\ IF g2[1,3].a # 1 \/ g2[1,3].a # 1
       THEN Assert(FALSE, "Test 23 Failed")
       ELSE Print("Test 23 OK", TRUE)

  /\ IF g1[1,2].a # 22 \/ g1[1,2].a # 22
       THEN Assert(FALSE, "Test 24 Failed")
       ELSE Print("Test 24 OK", TRUE)

  /\ IF g2[1,2].a # 22 \/ g2[1,2].a # 22
       THEN Assert(FALSE, "Test 25 Failed")
       ELSE Print("Test 25 OK", TRUE)

  /\ IF f5[3,4,5] # 12
       THEN Assert(FALSE, "Test 26 Failed")
       ELSE Print("Test 26 OK", TRUE)

  /\ IF f5[<<3,4,5>>] # 12
       THEN Assert(FALSE, "Test 27 Failed")
       ELSE Print("Test 27  OK", TRUE)

  /\ IF f6[1, 2, 3, <<4,5,6>>, 7] # 140
       THEN Assert(FALSE, "Test 28 Failed")
       ELSE Print("Test 28 OK", TRUE)

  /\ IF f6[<<1, 2, 3, <<4,5,6>>, 7>>] # 140
       THEN Assert(FALSE, "Test 29 Failed")
       ELSE Print("Test 29 OK", TRUE)

  /\ IF [i, j, k \in Int |-> i+j+k][3,4,5] # 12
       THEN Assert(FALSE, "Test 30 Failed")
       ELSE Print("Test 30 OK", TRUE)

  /\ IF [i, j, k \in Int |-> i+j+k][<<3,4,5>>] # 12
       THEN Assert(FALSE, "Test 31 Failed")
       ELSE Print("Test 31 OK", TRUE)




=========================================
