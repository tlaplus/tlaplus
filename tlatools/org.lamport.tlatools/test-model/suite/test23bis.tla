--------------- MODULE test23 -------------

EXTENDS Naturals, FiniteSets, Bags, TLC

VARIABLES x

(* S == {"a"} *)
S == {"a", "b", "c"} 

B1 == SetToBag(S)
B2 == BagCup(SetToBag(S), SetToBag({"a"}))
B3 == [i \in S |-> 3]
B4 == BagUnion({B1, B2, B3})
B9 == BagCup(SetToBag(S), SetToBag({"a"}))

F1(e) == CASE e = "a" -> "fa"
           [] e = "b" -> "fa"
           [] e = "c" -> "fc"
           [] e = "d" -> "fc"

Init == /\ Print("Computing Init", TRUE) 
        /\ x = 1

Next == UNCHANGED x

Inv ==
  /\ Print("Computing Inv", TRUE) 
  /\ Print(<<"B1", B1>>, TRUE)
  /\ Print(SetToBag({"a"}), TRUE)

  /\ LET B7    == (DOMAIN B1) \cup (DOMAIN SetToBag({"a"})) 
         e1(e, BB) == (IF e \in DOMAIN BB THEN BB[e] ELSE 0)
     IN /\ IF B7 = {}
            THEN Assert(FALSE, "Failed Test 0a")
            ELSE Print("Test 0a OK", TRUE)

        /\ IF [e \in B7 |-> 2]["a"] # 2
             THEN Assert(FALSE, "Failed Test 0b")
             ELSE Print("Test 0b OK", TRUE)

        /\ IF [e \in B7 |-> e1(e, B1)]["a"] # 1
             THEN Assert(FALSE, "Failed Test 0c")
             ELSE Print("Test 0c OK", TRUE)

        /\ IF [e \in B7 |-> e1(e, SetToBag({"a"}))]["a"] # 1
             THEN Assert(FALSE, "Failed Test 0d")
             ELSE Print("Test 0d OK", TRUE)

        /\ IF [e \in B7 |-> e1(e, B1) + e1(e,SetToBag({"a"}))]["a"] # 2
             THEN Assert(FALSE, "Failed Test 0e")
             ELSE Print("Test 0e OK", TRUE)

  /\ IF B9["a"] # 2
       THEN Assert(FALSE, "Failed Test 1aa")
       ELSE Print("Test 1aa OK", TRUE)
  /\ Print("Finished test 1aa", TRUE)

  /\ IF B2["a"] # 2
       THEN Assert(FALSE, "Failed Test 1a")
       ELSE Print("Test 1a OK", TRUE)
  /\ Print("Finished test 1a", TRUE)

  /\ IF BagToSet(B9) # S
       THEN Assert(FALSE, "Failed Test 1b")
       ELSE Print("Test 1b OK", TRUE)

  /\ IF BagToSet(B2) # S
       THEN Assert(FALSE, "Failed Test 1c")
       ELSE Print("Test 1c OK", TRUE)

  /\ IF BagToSet(B1 -- SetToBag({"a"})) # {"c", "b"}
       THEN Assert(FALSE, "Failed Test 2")
       ELSE Print("Test 2 OK", TRUE)

  /\ IF BagToSet(B3) # BagToSet(B1)
       THEN Assert(FALSE, "Failed Test 3")
       ELSE Print("Test 3 OK", TRUE)

  /\ IF BagIn("a", B1 -- SetToBag({"a"}))
       THEN Assert(FALSE, "Failed Test 4")
       ELSE Print("Test 4 OK", TRUE)

  /\ IF ~BagIn("a", B2)
       THEN Assert(FALSE, "Failed Test 5")
       ELSE Print("Test 5 OK", TRUE)

  /\ IF EmptyBag # B1 -- B1
       THEN Assert(FALSE, "Failed Test 6")
       ELSE Print("Test 6 OK", TRUE)

  /\ IF ~(B1 \sqsubseteq B2)
       THEN Assert(FALSE, "Failed Test 7")
       ELSE Print("Test 7 OK", TRUE)

  /\ IF ~(B2 \sqsubseteq B3)
       THEN Assert(FALSE, "Failed Test 8")
       ELSE Print("Test 8 OK", TRUE)

  /\ IF B2 \sqsubseteq B1
       THEN Assert(FALSE, "Failed Test 9")
       ELSE Print("Test 9 OK", TRUE)

  /\ IF BagCup(B1, SetToBag({"d"})) \sqsubseteq B1
       THEN Assert(FALSE, "Failed Test 10")
       ELSE Print("Test 10 OK", TRUE)

  /\ IF ~(B1 \sqsubseteq (B1 ++ SetToBag({"d"})) )
       THEN Assert(FALSE, "Failed Test 11")
       ELSE Print("Test 11 OK", TRUE)

  /\ IF BagToSet(B2 ++ SetToBag({"d"})) # S \cup {"d"}
       THEN Assert(FALSE, "Failed Test 12")
       ELSE Print("Test 12 OK", TRUE)

  /\ IF Cardinality(SubBag(B1)) # Cardinality(SUBSET S)
       THEN Assert(FALSE, "Failed Test 13")
       ELSE Print("Test 13 OK", TRUE)

  /\ IF Cardinality(SubBag(B3)) # 64
       THEN Assert(FALSE, "Failed Test 14")
       ELSE Print("Test 14 OK", TRUE)

  /\ IF CopiesIn("fa", BagOfAll(F1, B1)) # 2
       THEN Assert(FALSE, "Failed Test 15")
       ELSE Print("Test 15 OK", TRUE)

  /\ IF CopiesIn("a", BagOfAll(F1, B1)) # 0
       THEN Assert(FALSE, "Failed Test 16")
       ELSE Print("Test 16 OK", TRUE)

  /\ IF CopiesIn("fa", BagOfAll(F1, B3)) # 6
       THEN Assert(FALSE, "Failed Test 17")
       ELSE Print("Test 17 OK", TRUE)

  /\ IF BagCardinality(B1) # 3
       THEN Assert(FALSE, "Failed Test 18")
       ELSE Print("Test 18 OK", TRUE)

  /\ IF BagCardinality(B3) # 9
       THEN Assert(FALSE, "Failed Test 19")
       ELSE Print("Test 19 OK", TRUE)

==========================================================================


=============================================================================
