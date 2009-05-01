--------------- MODULE test2 -------------

(* test equality of various representations of functions. *)

EXTENDS Naturals, TLC

VARIABLE x
CONSTANT a, b, c
f == [i \in {1,2}, j \in {3,4} |-> i+j]
g == [p \in {1,2} \X {3,4} |-> p[1] + p[2]]
h == [i \in {1,2} |-> [j \in {3,4} |-> i+j]]

m == [i \in {3,4} |-> <<i, 7>>]


Type == x \in {1}
Inv  == 
 /\ TRUE

 /\ IF [i \in {3, 2, 1} |-> i+2] # <<3, 4, 5>>
      THEN Assert(FALSE, "Failed Test 1") 
      ELSE Print("Test 1 OK", TRUE)

 /\ IF [i \in {"a", "b", "c"} |-> 
         CASE i = "a" -> 1 [] i = "b" -> 2 [] i = "c" -> 3]
         # [c |-> 3, a |-> 1, b |-> 2]
      THEN Assert(FALSE, "Failed Test 2")
      ELSE Print("Test 2 OK", TRUE)

 /\ IF [c |-> 3, a |-> 1, b |-> 2] # 
        [[a |-> 1, b |-> 3, c |-> 4] EXCEPT !.b =2 , !.c=3]
      THEN Assert(FALSE, "Failed Test 3") 
      ELSE Print("Test 3 OK", TRUE)

 /\ IF <<3, 4, 5>> # [<<3, 42, 75>> EXCEPT ![3]=5, ![2]=4]
      THEN Assert(FALSE, "Failed Test 4") 
      ELSE Print("Test 4 OK", TRUE)

 /\ IF [i \in {3, 2, 1} |-> i+2] # [ j \in 1..3 |-> j+2]
      THEN Assert(FALSE, "Failed Test 5") 
      ELSE Print("Test 5 OK", TRUE)

 /\ IF [i \in {} |-> i] # <<>>
      THEN Assert(FALSE, "Failed Test 6") 
      ELSE Print("Test 6 OK", TRUE)

 /\ IF {i \in [{1,2} -> {a, b, c}] : i[1] = a} # {<<a, a>>, <<a, b>>, <<a, c>>}
      THEN Assert(FALSE, "Failed Test 7") 
      ELSE Print("Test 7 OK", TRUE)

 /\ IF [{"a", "bc"} -> {1, 2, 3}] # [bc : {1,2,3}, a : {1,2,3}]
      THEN Assert(FALSE, "Failed Test 8") 
      ELSE Print("Test 8 OK", TRUE)

 /\ IF f # g
      THEN Assert(FALSE, "Test 9 Failed")
      ELSE Print("Test 9 OK", TRUE)

 /\ IF f = h
      THEN Assert(FALSE, "Test 10 Failed")
      ELSE Print("Test 10 OK", TRUE)

 /\ IF [m EXCEPT ![4] = <<4, 8>>] # [m EXCEPT ![4][2] = @+1]
       THEN Assert(FALSE, "Test 11 Failed")
       ELSE Print("Test 11 OK", TRUE)

 /\ IF m#[m EXCEPT ![4][2] = 7]
       THEN Assert(FALSE, "Test 12 Failed")
       ELSE Print("Test 12 OK", TRUE)

 /\ IF f # [f EXCEPT ![1,3] = 4]
       THEN Assert(FALSE, "Test 13 Failed")
       ELSE Print("Test 13 OK", TRUE)

Init == x = 1

Next == UNCHANGED x
=========================================
