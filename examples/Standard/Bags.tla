------------------------------- MODULE Bags ---------------------------------
LOCAL INSTANCE Naturals

IsABag(B) ==  B \in [DOMAIN B -> {n \in Nat : n > 0}]

BagToSet(B) == DOMAIN B

SetToBag(S) == [e \in S |-> 1]  
  
BagIn(e,B) == e \in BagToSet(B)

EmptyBag == SetToBag({})

CopiesIn(e, B) ==  IF BagIn(e, B) THEN B[e] ELSE 0

B1 (+) B2  ==  
  [e \in (DOMAIN B1) \cup (DOMAIN B2) |-> CopiesIn(e, B1) + CopiesIn(e, B2)]
  
B1 (-) B2  == 
  LET B == [e \in DOMAIN B1 |-> CopiesIn(e, B1) - CopiesIn(e, B2)]
  IN  [e \in {d \in DOMAIN B : B[d] > 0} |-> B[e]]

LOCAL Sum(f) ==
  LET DSum[S \in SUBSET DOMAIN f] == LET elt == CHOOSE e \in S : TRUE
                                     IN  IF S = {} 
                                           THEN 0
                                           ELSE f[elt] + DSum[S \ {elt}]
  IN  DSum[DOMAIN f]

BagUnion(S) ==
  [e \in UNION {BagToSet(B) : B \in S} |-> Sum([B \in S |-> CopiesIn(e,B)])]

B1 \sqsubseteq B2  ==  /\ (DOMAIN B1) \subseteq (DOMAIN B2)
                       /\ \A e \in DOMAIN B1 : B1[e] \leq B2[e]

SubBag(B) ==
  LET AllBagsOfSubset == 
        UNION {[SB -> {n \in Nat : n > 0}] : SB \in SUBSET BagToSet(B)}  
  IN  {SB \in AllBagsOfSubset : \A e \in DOMAIN SB : SB[e] \leq B[e]}

BagOfAll(F(_), B) ==
  [e \in {F(d) : d \in BagToSet(B)} |-> 
     Sum( [d \in BagToSet(B) |-> IF F(d) = e THEN B[d] ELSE 0] ) ]

BagCardinality(B) == Sum(B)
=============================================================================
