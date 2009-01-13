----------------------------- MODULE Bags --------------------------------
(**************************************************************************)
(* A bag, also called a multiset, is a set that can contain multiple      *)
(* copies of the same element.  A bag can have infinitely many elements,  *)
(* but only finitely many copies of any single element.                   *)
(*                                                                        *)
(* We represent a bag in the usual way as a function whose range is a     *)
(* subset of the positive integers.  An element e belongs to bag B iff e  *)
(* is in the domain of B, in which case bag B contains B[e] copies of e.  *)
(**************************************************************************)
EXTENDS TLC
LOCAL INSTANCE Naturals

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

B1 (+) B2  ==
  (************************************************************************)
  (* The union of bags B1 and B2.                                         *)
  (************************************************************************)
  [e \in (DOMAIN B1) \cup (DOMAIN B2) |->
      (IF e \in DOMAIN B1 THEN B1[e] ELSE 0) 
    + (IF e \in DOMAIN B2 THEN B2[e] ELSE 0) ]
  
B1 (-) B2  == 
  (************************************************************************)
  (* The bag B1 with the elements of B2 removed--that is, with one copy   *)
  (* of an element removed from B1 for each copy of the same element in   *)
  (* B2.  If B2 has at least as many copies of e as B1, then B1 (-) B2    *)
  (* has no copies of e.                                                  *)
  (************************************************************************)
  LET B == [e \in DOMAIN B1 |-> IF e \in DOMAIN B2 THEN B1[e] - B2[e]
                                                   ELSE B1[e]]
  IN  [e \in {d \in DOMAIN B : B[d] > 0} |-> B[e]]

LOCAL Sum(f) ==
        (******************************************************************)
        (* The sum of f[x] for all x in DOMAIN f.  The definition assumes *)
        (* that f is a Nat-valued function and that f[x] equals 0 for all *)
        (* but a finite number of elements x in DOMAIN f.                 *)
        (******************************************************************)
        LET DSum[S \in SUBSET DOMAIN f] ==
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
  (*                                                                      *)
  (* The following definition is not the one described in the TLA+ book,  *)
  (* but rather one that TLC can evaluate.                                *)
  (************************************************************************)

  LET RemoveFromDom(x, f) == [y \in (DOMAIN f) \ {x} |-> f[y]]
      Combine(x, BagSet) == 
         BagSet \cup
          {[y \in (DOMAIN f) \cup {x} |-> IF y = x THEN i ELSE f[y]] :
                f \in BagSet, i \in 1..B[x]}
      Biggest == LET Range == {B[x] : x \in DOMAIN B}
                 IN  IF Range = {} THEN 0
                                   ELSE CHOOSE r \in Range :
                                           \A s \in Range : r \geq s
      RSB[BB \in UNION {[S -> 1..Biggest] : S \in SUBSET DOMAIN B}] ==
        IF BB = << >> THEN {<< >>}
                      ELSE LET x == CHOOSE x \in DOMAIN BB : TRUE
                           IN  Combine(x, RSB[RemoveFromDom(x, BB)])
  IN RSB[B]

  (*******************  Here is the definition from the TLA+ book. ********
  LET AllBagsOfSubset == 
        (******************************************************************)
        (* The set of all bags SB such that BagToSet(SB) \subseteq        *)
        (* BagToSet(B).                                                   *)
        (******************************************************************)
        UNION {[SB -> {n \in Nat : n > 0}] : SB \in SUBSET BagToSet(B)}  
  IN  {SB \in AllBagsOfSubset : \A e \in DOMAIN SB : SB[e] \leq B[e]}
  ***************************************************************************)

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
=============================================================================

(* Last modified on Fri 26 Jan 2007 at  8:45:03 PST by lamport *)

 6 Apr 99 : Modified version for standard module set
 7 Dec 98 : Corrected error found by Stephan Merz.
 6 Dec 98 : Modified comments based on suggestions by Lyle Ramshaw.
 5 Dec 98 : Initial version.
