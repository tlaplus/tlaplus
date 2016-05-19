--------------- MODULE test3 -------------

(* Test of function application. *)

EXTENDS Naturals, TLC

VARIABLE x
CONSTANT a, b, c

Type == x \in {1}
Inv  == 
 /\ TRUE

 /\ IF [i \in {3, 2, 1} |-> i+1][3] # 4
      THEN Assert(FALSE, "Test 1")
      ELSE Print("Test 1", TRUE)

 /\ IF <<a, b, c>>[2] # b
      THEN Assert(FALSE, "Test 2")
      ELSE Print("Test 2", TRUE)

 /\ IF [a |-> 1, b |-> 42, c |-> 99]["b"] # 42
      THEN Assert(FALSE, "Test 3" )
      ELSE Print("Test 3" , TRUE) 

 /\ IF [i \in Nat |-> i+1][3] # 4
      THEN Assert(FALSE, "Test 4" )
      ELSE Print("Test 4" , TRUE) 

 /\ IF [[i \in Nat |-> i+1] EXCEPT ![42] = 3, ![42] = 5][42] # 5
      THEN Assert(FALSE, "Test 5" )
      ELSE Print("Test 5" , TRUE) 

 /\ IF [[i \in Nat |-> i+1] EXCEPT ![42] = 3, ![42] = 5][79] # 80
      THEN Assert(FALSE, "Test 6" )
      ELSE Print("Test 6" , TRUE) 

 /\ IF [i \in Nat |-> [j \in Nat |-> 2*i + j]][5][3] # 13
      THEN Assert(FALSE, "Test 7" )
      ELSE Print("Test 7" , TRUE) 

 /\ IF [[i \in Nat |-> [j \in Nat |-> 2*i + j]] EXCEPT ![5] = 11][5] # 11
      THEN Assert(FALSE, "Test 8" )
      ELSE Print("Test 8" , TRUE) 
 /\ IF [[i \in Nat |-> [j \in Nat |-> 2*i + j]] EXCEPT ![5][3] = @+1][5][3] # 14
      THEN Assert(FALSE, "Test 9" )
      ELSE Print("Test 9" , TRUE) 

 /\ IF [[i \in Nat |-> [j \in Nat |-> 2*i + j]] 
            EXCEPT ![5][4] = @+2, ![5][3] = @+1][5][3] # 14
      THEN Assert(FALSE, "Test 10" )
      ELSE Print("Test 10" , TRUE) 

 /\ IF [[i \in Nat |-> [j \in Nat |-> 2*i + j]] 
            EXCEPT ![5][3] = @+1, ![5][4] = @+2][5][3] # 14
      THEN Assert(FALSE, "Test 11" )
      ELSE Print("Test 11" , TRUE) 

 /\ IF [[i \in Nat |-> [j \in Nat |-> 2*i + j]] 
        EXCEPT ![5][3] = @+1, ![5][3] = @+2][5][3] # 16
      THEN Assert(FALSE, "Test 12" )
      ELSE Print("Test 12" , TRUE) 

 /\ IF [i \in Nat, j \in STRING |-> <<i+1, j>>][22, "b"] # <<23, "b">>
      THEN Assert(FALSE, "Test 13" )
      ELSE Print("Test 13" , TRUE) 

 /\ IF [i \in Nat, j \in STRING |-> <<i+1, j>>][<<22, "b">>] # <<23, "b">>
      THEN Assert(FALSE, "Test 14" )
      ELSE Print("Test 14" , TRUE) 

 /\ IF [[i \in Nat, j \in STRING |-> <<i+1, j>>] 
        EXCEPT ![22, "c"] = 15] [22, "b"] # <<23, "b">>
      THEN Assert(FALSE, "Test 15" )
      ELSE Print("Test 15" , TRUE) 

 /\ IF [[i \in Nat, j \in STRING |-> <<i+1, j>>] 
          EXCEPT ![22, "c"] = 15] [22, "c"] # 15
      THEN Assert(FALSE, "Test 16" )
      ELSE Print("Test 16" , TRUE) 

 /\ IF [[i \in Nat, j \in STRING |-> <<i+1, j>>] 
        EXCEPT ![22, "c"] = 15] [<<22, "c">>] # 15
      THEN Assert(FALSE, "Test 17" )
      ELSE Print("Test 17" , TRUE) 

 /\ IF [[i \in Nat, j \in STRING |-> <<i+1, j>>] 
          EXCEPT ![22, "c"] = 15, ![22, "d"] = 33] [22, "c"] # 15
      THEN Assert(FALSE, "Test 18" )
      ELSE Print("Test 18" , TRUE) 

 /\ IF [[i \in Nat, j \in STRING |-> <<i+1, j>>] 
          EXCEPT ![22, "d"] = 33, ![22, "c"] = 15] [22, "c"] # 15
      THEN Assert(FALSE, "Test 19" )
      ELSE Print("Test 19" , TRUE) 

 /\ IF [[i \in Nat, j \in STRING |-> <<i+1, j>>] 
          EXCEPT ![22, "d"] = 33, ![22, "d"] = 15] [22, "d"] # 15
      THEN Assert(FALSE, "Test 20" )
      ELSE Print("Test 20" , TRUE) 

 /\ IF [[i \in Nat, j \in STRING |-> <<i+1, j>>] 
        EXCEPT ![22, "d"] = @[1]] [22, "d"] # 23
      THEN Assert(FALSE, "Test 21" )
      ELSE Print("Test 21" , TRUE) 


 /\ IF [[i \in Nat, j \in Nat |-> <<i+1, j>>] 
         EXCEPT ![22, 3] = @[1]] [22, 3] # 23
      THEN Assert(FALSE, "Test 22" )
      ELSE Print("Test 22" , TRUE) 

 /\ Print("Tests completed", TRUE)


 /\ Print("Tests completed", TRUE)

Init == x = 1

Next == UNCHANGED x
=========================================
