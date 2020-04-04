--------------- MODULE test5 -------------

(* test of Cartesian Product. *)

EXTENDS Integers, TLC

VARIABLE x
Type == x \in {1}
Init == x = 1
Next == UNCHANGED x

Inv  == 
  /\ IF {1, 2} \X {"a", "b"} # {<<1, "a">>, <<2, "a">>, <<2, "b">>, <<1, "b">>}
      THEN Assert(FALSE, "Test 1 failed")
      ELSE Print("Test 1 OK", TRUE)

  /\ IF [p \in Nat \X Int |-> p[1] - 2*p[2]][2, -3] # 8
      THEN Assert(FALSE, "Test 2 failed")
      ELSE Print("Test 2 OK", TRUE)

  /\ IF [p \in Int \X Int |-> p[1] - 2*p[2]][2, -3] # 8
      THEN Assert(FALSE, "Test 3 failed")
      ELSE Print("Test 3 OK", TRUE)

  /\ IF <<1, 3>> \notin Nat \X Nat
      THEN Assert(FALSE, "Test 4 failed")
      ELSE Print("Test 4 OK", TRUE)

  /\ IF <<1, 3>> \notin (Int \X Int)
      THEN Assert(FALSE, "Test 5 failed")
      ELSE Print("Test 5 OK", TRUE)

  /\ IF [1..2 -> {1, 2, 3}] \cap ({1} \X {2}) # {<<1,2>>}
      THEN Assert(FALSE, "Test 6 failed")
      ELSE Print("Test 6 OK", TRUE)

  /\ IF {<<1, 4>>, <<2,3>>} \notin SUBSET ({1,2} \X {3,4})
      THEN Assert(FALSE, "Test 7 failed")
      ELSE Print("Test 7 OK", TRUE)

  /\ IF <<1,3>> \notin {1,2,3} \X {2,3,4}
      THEN Assert(FALSE, "Test 8 failed")
      ELSE Print("Test 8 OK", TRUE)

  /\ IF {1, 2} \X {"a", "b"} \X {"c"} # 
           {<<1, "a", "c">>, <<2, "a", "c">>, <<2, "b", "c">>, <<1, "b", "c">>}
      THEN Assert(FALSE, "Test 9 failed")
      ELSE Print("Test 9 OK", TRUE)

  /\ IF [p \in Nat \X Int \X Nat |-> p[1] - 2*p[2] + p[3]][2, -3, 4] # 12
      THEN Assert(FALSE, "Test 10 failed")
      ELSE Print("Test 10 OK", TRUE)

  /\ IF [p \in Int \X Int \X Int |-> p[1] - 2*p[2] - p[3]][2, -3, -4] # 12
      THEN Assert(FALSE, "Test 11 failed")
      ELSE Print("Test 11 OK", TRUE)

  /\ IF <<1, 2, 3, 4>> \notin Nat \X Nat \X Nat \X Nat
      THEN Assert(FALSE, "Test 12 failed")
      ELSE Print("Test 12 OK", TRUE)

  /\ IF <<1, 2, 3, 4>> \notin (Int \X Int \X Int \X Int)
      THEN Assert(FALSE, "Test 13 failed")
      ELSE Print("Test 13 OK", TRUE)

  /\ IF [1..2 -> {1, 2, 3}] \cap ({1} \X {2}) # {<<1,2>>}
      THEN Assert(FALSE, "Test 14 failed")
      ELSE Print("Test 14 OK", TRUE)

  /\ IF {<<1, 4, 2>>, <<2,3,3>>} \notin SUBSET ({1,2} \X {3,4} \X {2, 3})
      THEN Assert(FALSE, "Test 15 failed")
      ELSE Print("Test 15 OK", TRUE)

  /\ IF <<1,3, 5>> \notin {1,2,3} \X {2,3,4} \X {5,6}
      THEN Assert(FALSE, "Test 16 failed")
      ELSE Print("Test 16 OK", TRUE)
  /\ \* Test 17 added 4 June 2014
     IF \/ {} \X {1,2} # {2,3,4} \X {}
        \/ {1, 2} \X {} \X {3,4} # {2} \X {4,4} \X {}
        \/ {1} \X {2} \X {} # {} \X {3,3}
      THEN Assert(FALSE, "Test 17 failed")
      ELSE Print("Test 17 OK", TRUE)
  /\ \* Test 18 added 12 Jun 2014
     IF \/ [a: {12}, b : {}] # [c: {22}, d: {xyz \in {1,2,3} : xyz < 0}]
        \/ [a: {12}, b : {}] # [c: {22}, d: 2..1]
        \/ [a: {12}, b : {}] # [c: {22}, d: {1,2,3} \cap 4..6]
        \/ [a: {12}, b : {}] # [c: {22}, d: {} \cup {xz \in {1,2,3} : xz < 0}]
        \/ [a: {12}, b : {}] # [c: {22}, d: {2,3,4} \X {}]
        \/ [a: {12}, b : {}] # [c: {22}, d: [a: {}, b : {1}]]
        \/ [a: {12}, b : {}] = [c: {22}, d: SUBSET {}]
        \/ [a: {12}, b : {}] # [c: {22}, d: UNION {}]
        \/ [a: {12}, b : {}] # [c: {22}, d: {2,3,4} \ 1..5]
        \/ [a: {12}, b : {}] # [c: {22}, d: [{1,2,3} -> {}]]
        \/ [a: {12}, b : {}] # [c: {22}, d: {}]
        \/ [a: {12}, b : {}] # [c: {22}, d: {xyz+1 : xyz \in 2..1}]
      THEN Assert(FALSE, "Test 18 failed")
      ELSE Print("Test 18 OK", TRUE)
  /\ \* Test 19 added 12 Jun 2014
     IF \/ {1} \X {2} \X {} # {22} \X  {xyz \in {1,2,3} : xyz < 0}
        \/ {1} \X {2} \X {} # {22} \X  (2..1)
        \/ {1} \X {2} \X {} # {22} \X  ({1,2,3} \cap (4..6))
        \/ {1} \X {2} \X {} # {22} \X ({} \cup {xz \in {1,2,3} : xz < 0})
        \/ {1} \X {2} \X {} # {22} \X ({2,3,4} \X {})
        \/ {1} \X {2} \X {} # {22} \X ([a: {}, b : {1}])
        \/ {1} \X {2} \X {} = {22} \X (SUBSET {})
        \/ {1} \X {2} \X {} # {22} \X (UNION {})
        \/ {1} \X {2} \X {} # {22} \X ({2,3,4} \ (1..5))
        \/ {1} \X {2} \X {} # {22} \X ([{1,2,3} -> {}])
        \/ {1} \X {2} \X {} # {22} \X ({})
        \/ {1} \X {2} \X {} # {22} \X ({xyz+1 : xyz \in 2..1})
      THEN Assert(FALSE, "Test 19 failed")
      ELSE Print("Test 19 OK", TRUE)
=========================================
