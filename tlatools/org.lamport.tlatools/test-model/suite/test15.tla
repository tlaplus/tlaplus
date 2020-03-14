--------------- MODULE test15 -------------
(* Test of handling the empty set *)

EXTENDS TLC, Naturals, Sequences

VARIABLE x
Type == x \in BOOLEAN
Init == x = TRUE
Next == UNCHANGED x



Inv ==  
  /\ IF SUBSET {} # {{}}
       THEN Assert(FALSE, "Test 1 Failed")
       ELSE Print("Test 1 OK", TRUE)

  /\ IF UNION {} # {}
       THEN Assert(FALSE, "Test 2 Failed")
       ELSE Print("Test 2 OK", TRUE)

  /\ IF {y \in {} : y = y} # {}
       THEN Assert(FALSE, "Test 3 Failed")
       ELSE Print("Test 3 OK", TRUE)

  /\ IF [y \in {} |-> y] # << >>
       THEN Assert(FALSE, "Test 4 Failed")
       ELSE Print("Test 4 OK", TRUE)

  /\ IF (\E S \in {} : TRUE) # FALSE
       THEN Assert(FALSE, "Test 5 Failed")
       ELSE Print("Test 5 OK", TRUE)

  /\ IF (\A S \in {} : FALSE) # TRUE
       THEN Assert(FALSE, "Test 6 Failed")
       ELSE Print("Test 6 OK", TRUE)

  /\ IF DOMAIN <<>> # {}
       THEN Assert(FALSE, "Test 7 Failed")
       ELSE Print("Test 7 OK", TRUE)

  /\ IF 1..0 # {}
       THEN Assert(FALSE, "Test 8 Failed")
       ELSE Print("Test 8 OK", TRUE)

  /\ IF <<>> \notin Seq({})
       THEN Assert(FALSE, "Test 9 Failed")
       ELSE Print("Test 9 OK", TRUE)

  /\ IF <<{}>> \in Seq ({})
       THEN Assert(FALSE, "Test 10 Failed")
       ELSE Print("Test 10 OK", TRUE)

  /\ IF \E S \in SUBSET {} : S # {}
       THEN Assert(FALSE, "Test 11 Failed")
       ELSE Print("Test 11 OK", TRUE)
  /\ IF [{} -> {1, 2, 3}] # {<<>>}
       THEN Assert(FALSE, "Test 12 Failed")
       ELSE Print("Test 12 OK", TRUE)

  /\ IF [{1, 2, 3} -> {}] # {}
       THEN Assert(FALSE, "Test 13 Failed")
       ELSE Print("Test 13 OK", TRUE)


  /\ IF (UNION {{1,2,3}, {}}) # (UNION {{1,2,3}}) 
       THEN Assert(FALSE, "Test 14 Failed")
       ELSE Print("Test 14 OK", TRUE)

  /\ IF 1..0 # {}
       THEN Assert(FALSE, "Test 15 Failed")
       ELSE Print("Test 15 OK", TRUE)

  /\ IF 1..0 # 5..2
       THEN Assert(FALSE, "Test 16 Failed")
       ELSE Print("Test 16 OK", TRUE)

=========================================
