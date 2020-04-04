--------------- MODULE test20 -------------

(* Test of ENABLED *)

EXTENDS Naturals, Sequences, TLC

VARIABLE x, y

Init == x = 1 /\ y = 1

Step(p) == x' = p

Foo(A) == ENABLED((x' = x) /\ (A'=x+1))

Next == 
  \/ /\ x'=x
     /\ y'=y

  \/ /\ Print("Test N1 begun", TRUE)
     /\ ~ENABLED (x'=2)
     /\ Assert(FALSE, "Test N1 Failed")

  \/ IF ENABLED (x'=2)
       THEN /\ Print("Test N2 Passed", TRUE)
            /\ UNCHANGED <<x, y>>
       ELSE Assert(FALSE, "Test N2 Failed")
  \/ IF ENABLED Step(17)
       THEN /\ Print("Test N3 Passed", TRUE)
            /\  UNCHANGED <<x, y>>
       ELSE Assert(FALSE, "Test N3 Failed")

  \/ IF \A p \in 1..3 : ENABLED Step(p)
       THEN /\ Print("Test N4 Passed", TRUE)
            /\  UNCHANGED <<x, y>>
       ELSE Assert(FALSE, "Test N4 Failed")

Inv == 
  /\ IF ENABLED <<x'=1 /\ y'=y>>_<<x,y>>
       THEN Assert(FALSE, "Test 1 Failed")
       ELSE Print("Test 1 OK", TRUE)

  /\ IF ~ ENABLED (x'="a" /\ y'=y)
       THEN Assert(FALSE, "Test 2 Failed")
       ELSE Print("Test 2 OK", TRUE)

  /\ IF ENABLED (x > 2)
       THEN Assert(FALSE, "Test 3 Failed")
       ELSE Print("Test 3 OK", TRUE)

  /\ IF ~ENABLED (x=1)
       THEN Assert(FALSE, "Test 4 Failed")
       ELSE Print("Test 4 OK", TRUE)

  /\ IF ENABLED ((x > 2) /\ Next)
       THEN Assert(FALSE, "Test 5 Failed")
       ELSE Print("Test 5 OK", TRUE)

  /\ IF ~ENABLED ((x=1) /\ Next)
       THEN Assert(FALSE, "Test 6 Failed")
       ELSE Print("Test 6 OK", TRUE)

  /\ IF ~ ENABLED (x'=1) 
       THEN Assert(FALSE, "Test 7 Failed")
       ELSE Print("Test 7 OK", TRUE)

  /\ IF Foo(x)
       THEN Assert(FALSE, "Test 8 Failed")
       ELSE Print("Test 8 OK", TRUE)

  /\ LET A == x
     IN  IF Foo(A) 
           THEN Assert(FALSE, "Test 9 Failed")
           ELSE Print("Test 9 OK", TRUE)

  /\ IF ~Foo(y) 
       THEN Assert(FALSE, "Test 10 Failed")
       ELSE Print("Test 10 OK", TRUE)

  /\ LET A == x
     IN  IF ~Foo(y) 
           THEN Assert(FALSE, "Test 11 Failed")
           ELSE Print("Test 11 OK", TRUE)


=========================================
