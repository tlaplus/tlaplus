--------------- MODULE test23 -------------

(* Test of definitions from the Bags module *)

EXTENDS Naturals, FiniteSets, TLC

IsABag(B) == 
  (************************************************************************)
  (* True iff B is a bag.                                                 *)
  (************************************************************************)
  B \in [DOMAIN B -> {n \in Nat : n > 0}]

BagToSet(B) == DOMAIN B
  (************************************************************************)
  (* The set of elements at least one copy of which is in B.              *)
  (************************************************************************)

SetToBag(S) == [e \in S |-> 1]  
  (************************************************************************)
  (* The bag that contains one copy of every element of the set S.        *)
  (************************************************************************)
  
BagIn(e,B) == e \in BagToSet(B)
  (************************************************************************)
  (* The \in operator for bags.                                           *)
  (************************************************************************)

EmptyBag == SetToBag({})

BagCup(B1, B2)  ==
  (************************************************************************)
  (* The union of bags B1 and B2.                                         *)
  (************************************************************************)
  [e \in (DOMAIN B1) \cup (DOMAIN B2) |->
      (IF e \in DOMAIN B1 THEN B1[e] ELSE 0) 
    + (IF e \in DOMAIN B2 THEN B2[e] ELSE 0) ]

B1 ++ B2 == BagCup(B1, B2)
  
BagDiff(B1, B2)  == 
  (************************************************************************)
  (* The bag B1 with the elements of B2 removed--that is, with one copy   *)
  (* of an element removed from B1 for each copy of the same element in   *)
  (* B2.  If B2 has at least as many copies of e as B1, then B1 -- B2    *)
  (* has no copies of e.                                                  *)
  (************************************************************************)
  LET B == [e \in DOMAIN B1 |-> IF e \in DOMAIN B2 THEN B1[e] - B2[e]
                                                   ELSE B1[e]]
  IN  [e \in {d \in DOMAIN B : B[d] > 0} |-> B[e]]

B1 -- B2 == BagDiff(B1, B2)

LOCAL Sum(f) ==
        (******************************************************************)
        (* The sum of f[x] for all x in DOMAIN f.  The definition assumes *)
        (* that f is a Nat-valued function and that f[x] equals 0 for all *)
        (* but a finite number of elements x in DOMAIN f.                 *)
        (******************************************************************)
        LET D == {e \in DOMAIN f : f[e] > 0}
            DSum[S \in SUBSET DOMAIN f] ==
               LET elt == CHOOSE e \in S : TRUE
               IN  IF S = {} THEN 0
                             ELSE f[elt] + DSum[S \ {elt}]
        IN  DSum[DOMAIN f]

BagUnion(S) ==
  (************************************************************************)
  (* The bag union of all elements of the set S of bags.                  *)
  (************************************************************************)
  [e \in UNION {BagToSet(B) : B \in S} |->
    Sum( [B \in S |-> IF BagIn(e, B) THEN B[e] ELSE 0] ) ]

B1 \sqsubseteq B2  ==
  (************************************************************************)
  (* The subset operator for bags.  B1 \sqsubseteq B2 iff, for all e, bag *)
  (* B2 has at least as many copies of e as bag B1 does.                  *)
  (************************************************************************)
  /\ (DOMAIN B1) \subseteq (DOMAIN B2)
  /\ \A e \in DOMAIN B1 : B1[e] \leq B2[e]

SubBag(B) ==
  (************************************************************************)
  (* The set of all subbags of bag B.                                     *)
  (************************************************************************)
  LET AllBagsOfSubset == 
        (******************************************************************)
        (* The set of all bags SB such that BagToSet(SB) \subseteq        *)
        (* BagToSet(B).                                                   *)
        (******************************************************************)
        UNION {[SB -> {n \in Nat : n > 0}] : SB \in SUBSET BagToSet(B)}  
  IN  {SB \in AllBagsOfSubset : \A e \in DOMAIN SB : SB[e] \leq B[e]}

BagOfAll(F(_), B) ==
  (************************************************************************)
  (* The bag analog of the set {F(x) : x \in B} for a set B. It's the bag *)
  (* that contains, for each element e of B, one copy of F(e) for every   *)
  (* copy of e in B. This defines a bag iff, for any value v, the set of  *)
  (* e in B such that F(e) = v is finite.                                 *)
  (************************************************************************)
  [e \in {F(d) : d \in BagToSet(B)} |-> 
     Sum( [d \in BagToSet(B) |-> IF F(d) = e THEN B[d] ELSE 0] ) ]

BagCardinality(B) ==
  (************************************************************************)
  (* If B is a finite bag (one such that BagToSet(B) is a finite set),    *)
  (* then this is its cardinality (the total number of copies of elements *)
  (* in B).  Its value is unspecified if B is infinite.                   *)
  (************************************************************************)
  Sum(B)

CopiesIn(e, B) ==
  (************************************************************************)
  (* If B is a bag, then CopiesIn(e, B) is the number of copies of e in   *)
  (* B. If ~BagIn(e, B), then CopiesIn(e, B) = 0.                         *)
  (************************************************************************)
  IF BagIn(e, B) THEN B[e] ELSE 0



Max(a, b) == IF a < b THEN b ELSE a
MaxCopies(B) ==
  (*************************************************************************)
  (* Maximum of B[e] s.t. e \in DOMAIN B                                   *)
  (*************************************************************************)
  LET MC[S \in SUBSET(DOMAIN B)] ==
        LET elt == CHOOSE elt \in S : TRUE
        IN  IF S = {} THEN 0
                      ELSE Max(B[elt], MC[S \ {elt}])
  IN MC[DOMAIN B]

MCSubBag(B) ==
  (*************************************************************************)
  (* Definition of SubBag that TLC can handle.                             *)
  (*************************************************************************)
  LET AllBagsOfSubset == 
        (******************************************************************)
        (* The set of all bags SB such that BagToSet(SB) \subseteq        *)
        (* BagToSet(B).                                                   *)
        (******************************************************************)
        UNION {[SB -> {n \in 1..MaxCopies(B) : n > 0}] : SB \in SUBSET BagToSet(B)}  
  IN  {SB \in AllBagsOfSubset : \A e \in DOMAIN SB : SB[e] \leq B[e]}
         
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
