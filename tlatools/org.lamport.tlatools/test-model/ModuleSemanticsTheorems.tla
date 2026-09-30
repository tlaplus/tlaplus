---------------------- MODULE ModuleSemanticsTheorems -----------------------
\* Representation-independent proofs of the propositions that
\* ModuleSemanticsAssume.tla asks TLC to evaluate.
EXTENDS Integers, TLAPS

Cases == INSTANCE ModuleSemanticsCases

\* Bags defines BagCardinality by a recursive function, which is a CHOOSE,
\* so compute it from its defining equation, which G witnesses.
LEMMA BagCardinalityPair ==
  ASSUME NEW f, NEW p, NEW q, p # q, DOMAIN f = {p, q},
         f[p] \in Int, f[q] \in Int
  PROVE  Cases!BagCardinality(f) = f[p] + f[q]
  <1> DEFINE Body(D) ==
        [S \in SUBSET DOMAIN f |->
           IF S = {} THEN 0
                     ELSE f[CHOOSE e \in S : TRUE]
                          + D[S \ {CHOOSE e \in S : TRUE}]]
  <1> DEFINE G ==
        [S \in SUBSET DOMAIN f |->
           (IF p \in S THEN f[p] ELSE 0) + (IF q \in S THEN f[q] ELSE 0)]
  <1>1. G = Body(G)
    <2> SUFFICES ASSUME NEW S \in SUBSET DOMAIN f
                 PROVE  G[S] = Body(G)[S]
      OBVIOUS
    <2>1. CASE S = {}
      BY <2>1
    <2>2. CASE S # {}
      <3> DEFINE c == CHOOSE e \in S : TRUE
      <3>1. c \in S
        BY <2>2
      <3>2. c = p \/ c = q
        BY <3>1
      <3>3. S \ {c} \in SUBSET DOMAIN f
        OBVIOUS
      <3>4. Body(G)[S] = f[c] + G[S \ {c}]
        BY <2>2
      <3>5. QED BY <3>2, <3>3, <3>4, SMT
    <2>3. QED BY <2>1, <2>2
  <1>2. ASSUME NEW D, D = Body(D)
        PROVE  D[{p, q}] = f[p] + f[q]
    <2>1. D[{}] = 0
      BY <1>2
    <2>2. D[{p}] = f[p]
      <3>1. (CHOOSE e \in {p} : TRUE) = p /\ {p} \ {p} = {}
        OBVIOUS
      <3>2. QED BY <1>2, <2>1, <3>1, SMT
    <2>3. D[{q}] = f[q]
      <3>1. (CHOOSE e \in {q} : TRUE) = q /\ {q} \ {q} = {}
        OBVIOUS
      <3>2. QED BY <1>2, <2>1, <3>1, SMT
    <2> DEFINE c == CHOOSE e \in {p, q} : TRUE
    <2>4. D[{p, q}] = f[c] + D[{p, q} \ {c}]
      BY <1>2
    <2>5. \/ c = p /\ {p, q} \ {c} = {q}
          \/ c = q /\ {p, q} \ {c} = {p}
      OBVIOUS
    <2>6. QED BY <2>2, <2>3, <2>4, <2>5, SMT
  <1> DEFINE D0 == CHOOSE D : D = Body(D)
  <1>3. D0 = Body(D0)
    BY <1>1
  <1>4. D0[{p, q}] = f[p] + f[q]
    BY <1>2, <1>3
  <1>5. Cases!BagCardinality(f) = D0[DOMAIN f]
    BY DEF Cases!BagCardinality
  <1>6. QED BY <1>4, <1>5

LEMMA BagCardinalityConstPair ==
  ASSUME NEW p, NEW q, p # q, NEW a \in Int
  PROVE  Cases!BagCardinality([x \in {p, q} |-> a]) = a + a
  BY BagCardinalityPair

LEMMA BagUnionSingletons ==
  ASSUME NEW e, NEW a \in Int, NEW b \in Int, a # b
  PROVE  Cases!BagUnion({[x \in {e} |-> a], [x \in {e} |-> b]})
           = [x \in {e} |-> a + b]
  <1> DEFINE B1 == [x \in {e} |-> a]
             B2 == [x \in {e} |-> b]
             S  == {B1, B2}
             g  == [B \in S |-> IF Cases!BagIn(e, B) THEN B[e] ELSE 0]
  <1>1. B1 # B2
    OBVIOUS
  <1>2. g[B1] = a /\ g[B2] = b
    BY <1>1 DEF Cases!BagIn, Cases!BagToSet
  <1>3. Cases!BagCardinality(g) = a + b
    BY <1>1, <1>2, BagCardinalityPair
  <1>4. UNION {Cases!BagToSet(B) : B \in S} = {e}
    BY DEF Cases!BagToSet
  <1>5. DOMAIN Cases!BagUnion(S) = {e}
    BY <1>4 DEF Cases!BagUnion
  <1>6. Cases!BagUnion(S)[e] = Cases!BagCardinality(g)
    BY <1>4 DEF Cases!BagUnion, Cases!BagCardinality
  <1>7. QED BY <1>3, <1>5, <1>6 DEF Cases!BagUnion

THEOREM BagCardPair == Cases!BagCardPair
  BY BagCardinalityConstPair, SMT DEF Cases!BagCardPair

THEOREM BagCupPair == Cases!BagCupPair
  BY DEF Cases!BagCupPair, Cases!\oplus

THEOREM BagUnionPair == Cases!BagUnionPair
  <1>1. Cases!BagUnion({[x \in {1} |-> 2], [x \in {1} |-> 1]})
          = [x \in {1} |-> 2 + 1]
    BY BagUnionSingletons
  <1>2. QED BY <1>1, SMT DEF Cases!BagUnionPair

THEOREM BagCardMax == Cases!BagCardMax
  <1>1. Cases!MaxInt \in Int
    BY DEF Cases!MaxInt
  <1>2. Cases!BagCardinality([x \in {1, 2} |-> Cases!MaxInt])
          = Cases!MaxInt + Cases!MaxInt
    BY <1>1, BagCardinalityConstPair
  <1>3. QED BY <1>2, SMT DEF Cases!BagCardMax, Cases!MaxInt

THEOREM BagCupMax == Cases!BagCupMax
  BY DEF Cases!BagCupMax, Cases!\oplus, Cases!MaxInt

THEOREM BagUnionMax == Cases!BagUnionMax
  <1>1. Cases!MaxInt \in Int /\ Cases!MaxInt # 2
    BY SMT DEF Cases!MaxInt
  <1>2. Cases!BagUnion({[x \in {1} |-> Cases!MaxInt], [x \in {1} |-> 2]})
          = [x \in {1} |-> Cases!MaxInt + 2]
    BY <1>1, BagUnionSingletons
  <1>3. QED BY <1>2, SMT DEF Cases!BagUnionMax, Cases!MaxInt
=============================================================================
