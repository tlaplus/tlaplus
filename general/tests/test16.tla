--------------- MODULE test16 -------------
(* Test of handling of one-tuples *)

EXTENDS TLC, Naturals, Sequences

VARIABLE x
Type == x \in BOOLEAN
Init == x = TRUE
Next == UNCHANGED x

S == {<<y>> : y \in {1, 2, 3, 4}}

Inv ==  

  /\ IF <<1>> \notin S
       THEN Assert(FALSE, "Test 1 Failed")
       ELSE Print("Test 1 OK", TRUE)

  /\ IF ~(\E <<y>> \in S : y = 2) 
       THEN Assert(FALSE, "Test 2 Failed")
       ELSE Print("Test 2 OK", TRUE)

  /\ IF ~(\E y \in S : y[1] = 2) 
       THEN Assert(FALSE, "Test 3 Failed")
       ELSE Print("Test 3 OK", TRUE)

  /\ IF {<<y>> \in S : y > 3} # {<<4>>}
       THEN Assert(FALSE, "Test 4 Failed")
       ELSE Print("Test 4 OK", TRUE)

  /\ IF <<1>> \o <<2>> # <<1, 2>>
       THEN Assert(FALSE, "Test 5 Failed")
       ELSE Print("Test 5 OK", TRUE)

  /\ IF [<<y>> \in S |-> y+1][<<2>>] # 3
       THEN Assert(FALSE, "Test 6 Failed")
       ELSE Print("Test 6 OK", TRUE)


=========================================
