--------------- MODULE test14 -------------

(* Test of IF and CASE and nested junctions *)

EXTENDS Integers, TLC, FiniteSets, Sequences


VARIABLE x
Type == x \in BOOLEAN
Init == x = TRUE
Next == UNCHANGED x

Inv  ==  

  /\ IF (IF TRUE THEN IF FALSE THEN 3 ELSE 2 ELSE 1) # 2
       THEN Assert(FALSE, "Test 1 Failed")
       ELSE Print("Test 1 OK", TRUE)

  /\ IF (CASE FALSE -> 1 [] TRUE -> CASE FALSE -> 2 [] TRUE -> 3 [] OTHER -> 4)
          # 3
       THEN Assert(FALSE, "Test 2 Failed")
       ELSE Print("Test 2 OK", TRUE)

  /\ IF (CASE FALSE -> 1 [] FALSE -> CASE FALSE -> 2 [] TRUE -> 3 
               [] OTHER -> 4 [] TRUE -> 5) # 5
       THEN Assert(FALSE, "Test 3 Failed")
       ELSE Print("Test 3 OK", TRUE)

  /\ IF (CASE FALSE -> 1 [] TRUE -> CASE FALSE -> 2 [] FALSE -> 3 
          [] OTHER -> 4 [] TRUE -> 5) # 4
       THEN Assert(FALSE, "Test 4 Failed")
       ELSE Print("Test 4 OK", TRUE)

  /\ IF (CASE FALSE -> 1 [] FALSE -> CASE TRUE -> 2 [] TRUE -> 3 
                 [] OTHER -> 4 [] OTHER -> 5) # 5
       THEN Assert(FALSE, "Test 5 Failed")
       ELSE Print("Test 5 OK", TRUE)

  /\ IF (CASE TRUE -> 1 [] TRUE -> CASE TRUE -> 2 [] TRUE -> 3 
            [] OTHER -> 4 [] OTHER -> 5) \notin {1, 2, 3}
       THEN Assert(FALSE, "Test 6 Failed")
       ELSE Print("Test 6 OK", TRUE)

  /\ IF  ~ \/ /\ 1=3
              /\ "a" = 1
           \/ /\ 1 = 2
              /\ "b" = 1
           \/ /\ 1 = 1
              /\ 2 = 2
           \/ "c" = 1
       THEN Assert(FALSE, "Test 7 Failed")
       ELSE Print("Test 7 OK", TRUE)

=========================================
