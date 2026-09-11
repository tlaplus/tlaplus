------------------------------ MODULE KSubsetTheorems ------------------------
\* Proofs of the propositions in KSubsetCases that KSubsetAssume asks TLC to
\* evaluate, in the same order. General lemmas quantify over k and the base
\* set explicitly.
\*
\* kSubset is defined locally because TLAPS does not read FiniteSetsExt from
\* CommunityModules.jar.
\*
\* TLC does not parse this module. Check it from tlatools/org.lamport.tlatools
\* with:
\*   tlapm --strict -I test-model test-model/KSubsetTheorems.tla
\*
\* See https://github.com/tlaplus/tlaplus/issues/1415 and
\* https://github.com/tlaplus/tlaplus/issues/1424
EXTENDS FiniteSets, FiniteSetTheorems, Integers

kSubset(k, S) == { s \in SUBSET S : Cardinality(s) = k }

Cases == INSTANCE KSubsetCases WITH TLCFP <- LAMBDA value : value

-----------------------------------------------------------------------------

LEMMA IntervalThree == 1..3 = {1, 2, 3}
  OBVIOUS

LEMMA PowerSetThree ==
  Cases!P = {{}, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}}
  BY IntervalThree DEF Cases!P

LEMMA CardinalitiesThree ==
  /\ Cardinality({})        = 0
  /\ Cardinality({1})       = 1
  /\ Cardinality({2})       = 1
  /\ Cardinality({3})       = 1
  /\ Cardinality({1, 2})    = 2
  /\ Cardinality({1, 3})    = 2
  /\ Cardinality({2, 3})    = 2
  /\ Cardinality({1, 2, 3}) = 3
  <1>1. \A x : Cardinality({x}) = 1
    BY FS_Singleton
  <1>2. \A x, y : x # y => (IsFiniteSet({x, y}) /\ Cardinality({x, y}) = 2)
    <2> SUFFICES ASSUME NEW x, NEW y, x # y
                 PROVE  IsFiniteSet({x, y}) /\ Cardinality({x, y}) = 2
      OBVIOUS
    <2>1. IsFiniteSet({y}) /\ Cardinality({y}) = 1
      BY FS_Singleton
    <2>2. x \notin {y}
      OBVIOUS
    <2>3. IsFiniteSet({y} \cup {x}) /\ Cardinality({y} \cup {x}) = 2
      BY <2>1, <2>2, FS_AddElement
    <2>4. QED BY <2>3
  <1>3. Cardinality({1, 2, 3}) = 3
    <2>1. IsFiniteSet({2, 3}) /\ Cardinality({2, 3}) = 2
      BY <1>2
    <2>2. 1 \notin {2, 3}
      OBVIOUS
    <2>3. Cardinality({2, 3} \cup {1}) = 3
      BY <2>1, <2>2, FS_AddElement
    <2>4. QED BY <2>3
  <1>4. QED BY <1>1, <1>2, <1>3, FS_EmptySet

LEMMA KOneThree == Cases!K1 = {{1}, {2}, {3}}
  BY PowerSetThree, CardinalitiesThree DEF Cases!K1, Cases!P, kSubset

LEMMA KTwoThree == Cases!K2 = {{1, 2}, {1, 3}, {2, 3}}
  BY PowerSetThree, CardinalitiesThree DEF Cases!K2, Cases!P, kSubset

LEMMA KThreeThree == Cases!K3 = {{1, 2, 3}}
  BY PowerSetThree, CardinalitiesThree DEF Cases!K3, Cases!P, kSubset

LEMMA KZeroThreeSym == Cases!K0Sym = Cases!K0
  BY IntervalThree DEF Cases!K0Sym, Cases!K0

LEMMA KOneThreeSym == Cases!K1Sym = Cases!K1
  BY IntervalThree DEF Cases!K1Sym, Cases!K1

LEMMA KTwoThreeSym == Cases!K2Sym = Cases!K2
  BY IntervalThree DEF Cases!K2Sym, Cases!K2

LEMMA KThreeThreeSym == Cases!K3Sym = Cases!K3
  BY IntervalThree DEF Cases!K3Sym, Cases!K3

LEMMA KZeroThree == Cases!K0 = {{}}
  BY PowerSetThree, CardinalitiesThree DEF Cases!K0, Cases!P, kSubset

-----------------------------------------------------------------------------
\* Cardinalities of k-subset families and of their elements.

THEOREM CardKZero == Cases!CardKZero
  BY KZeroThree, FS_Singleton DEF Cases!CardKZero

THEOREM CardKOne == Cases!CardKOne
  <1>1. Cardinality({{1}, {2}, {3}}) = 3
    <2>1. IsFiniteSet({{2}, {3}}) /\ Cardinality({{2}, {3}}) = 2
      <3>1. IsFiniteSet({{3}}) /\ Cardinality({{3}}) = 1
        BY FS_Singleton
      <3>2. {2} \notin {{3}}
        OBVIOUS
      <3>3. QED BY <3>1, <3>2, FS_AddElement
    <2>2. {1} \notin {{2}, {3}}
      OBVIOUS
    <2>3. QED BY <2>1, <2>2, FS_AddElement
  <1>2. QED BY <1>1, KOneThree DEF Cases!CardKOne

THEOREM CardKTwo == Cases!CardKTwo
  <1>1. Cardinality({{1, 2}, {1, 3}, {2, 3}}) = 3
    <2>1. IsFiniteSet({{1, 3}, {2, 3}}) /\ Cardinality({{1, 3}, {2, 3}}) = 2
      <3>1. IsFiniteSet({{2, 3}}) /\ Cardinality({{2, 3}}) = 1
        BY FS_Singleton
      <3>2. {1, 3} \notin {{2, 3}}
        OBVIOUS
      <3>3. QED BY <3>1, <3>2, FS_AddElement
    <2>2. {1, 2} \notin {{1, 3}, {2, 3}}
      OBVIOUS
    <2>3. QED BY <2>1, <2>2, FS_AddElement
  <1>2. QED BY <1>1, KTwoThree DEF Cases!CardKTwo

THEOREM CardKThree == Cases!CardKThree
  BY KThreeThree, FS_Singleton DEF Cases!CardKThree

THEOREM KTwoElementCardinality == Cases!KTwoElementCardinality
  BY DEF Cases!KTwoElementCardinality, Cases!K2, kSubset

THEOREM KSubsetTooLargeEmpty == Cases!KSubsetTooLargeEmpty
  BY PowerSetThree, CardinalitiesThree
     DEF Cases!KSubsetTooLargeEmpty, Cases!P, kSubset

THEOREM KSubsetNegativeEmpty == Cases!KSubsetNegativeEmpty
  BY PowerSetThree, CardinalitiesThree
     DEF Cases!KSubsetNegativeEmpty, Cases!P, kSubset

THEOREM CardKSubsetTooLarge == Cases!CardKSubsetTooLarge
  BY KSubsetTooLargeEmpty, FS_EmptySet
     DEF Cases!CardKSubsetTooLarge, Cases!KSubsetTooLargeEmpty

THEOREM CardKSubsetNegative == Cases!CardKSubsetNegative
  BY KSubsetNegativeEmpty, FS_EmptySet
     DEF Cases!CardKSubsetNegative, Cases!KSubsetNegativeEmpty

THEOREM EmptyBaseKZeroUnit == Cases!EmptyBaseKZeroUnit
  BY FS_EmptySet, FS_Singleton DEF Cases!EmptyBaseKZeroUnit, kSubset

THEOREM EmptyBaseKOneEmpty == Cases!EmptyBaseKOneEmpty
  BY FS_EmptySet DEF Cases!EmptyBaseKOneEmpty, kSubset

THEOREM EmptyEqKSubsetTooLarge == Cases!EmptyEqKSubsetTooLarge
  BY KSubsetTooLargeEmpty
     DEF Cases!EmptyEqKSubsetTooLarge, Cases!KSubsetTooLargeEmpty

THEOREM EmptyEqKSubsetNegative == Cases!EmptyEqKSubsetNegative
  BY KSubsetNegativeEmpty
     DEF Cases!EmptyEqKSubsetNegative, Cases!KSubsetNegativeEmpty

THEOREM KZeroNestedEnumeration == Cases!KZeroNestedEnumeration
  BY KZeroThree DEF Cases!KZeroNestedEnumeration

THEOREM EmptyInKZeroNat == Cases!EmptyInKZeroNat
  BY FS_EmptySet DEF Cases!EmptyInKZeroNat, kSubset

THEOREM EmptyNotInKSubsetNegativeNat ==
  Cases!EmptyNotInKSubsetNegativeNat
  BY FS_EmptySet DEF Cases!EmptyNotInKSubsetNegativeNat, kSubset

THEOREM SingletonNotInKZeroNat == Cases!SingletonNotInKZeroNat
  BY FS_Singleton DEF Cases!SingletonNotInKZeroNat, kSubset

THEOREM SingletonInKOneNat == Cases!SingletonInKOneNat
  BY FS_Singleton DEF Cases!SingletonInKOneNat, kSubset

THEOREM EmptyInKZeroString == Cases!EmptyInKZeroString
  BY FS_EmptySet DEF Cases!EmptyInKZeroString, kSubset

THEOREM EmptyNotInKSubsetNegativeString ==
  Cases!EmptyNotInKSubsetNegativeString
  BY FS_EmptySet DEF Cases!EmptyNotInKSubsetNegativeString, kSubset

LEMMA KZeroNatDiffKOneNat ==
  kSubset(0, Nat) # kSubset(1, Nat)
  <1>1. {} \in kSubset(0, Nat)
    BY FS_EmptySet DEF kSubset
  <1>2. {} \notin kSubset(1, Nat)
    BY FS_EmptySet DEF kSubset
  <1>3. QED BY <1>1, <1>2

-----------------------------------------------------------------------------
\* Membership in k-subsets and inclusion in the base set's power set.

THEOREM PairInKTwo == Cases!PairInKTwo
  BY KTwoThree DEF Cases!PairInKTwo

THEOREM SingletonNotInKTwo == Cases!SingletonNotInKTwo
  BY KTwoThree DEF Cases!SingletonNotInKTwo

THEOREM EmptyNotInKTwo == Cases!EmptyNotInKTwo
  BY KTwoThree DEF Cases!EmptyNotInKTwo

THEOREM EmptyInKZero == Cases!EmptyInKZero
  BY KZeroThree DEF Cases!EmptyInKZero

THEOREM ScalarNotInKSubsetNegative == Cases!ScalarNotInKSubsetNegative
  BY KSubsetNegativeEmpty, FS_EmptySet
     DEF Cases!ScalarNotInKSubsetNegative, Cases!KSubsetNegativeEmpty

THEOREM ScalarNotInKSubsetTooLarge == Cases!ScalarNotInKSubsetTooLarge
  BY KSubsetTooLargeEmpty, FS_EmptySet
     DEF Cases!ScalarNotInKSubsetTooLarge, Cases!KSubsetTooLargeEmpty

THEOREM KSubsetInPowerSet ==
  ASSUME NEW k, NEW S
  PROVE  kSubset(k, S) \subseteq SUBSET S
  BY DEF kSubset

THEOREM KOneInPowerSet == Cases!KOneInPowerSet
  BY KSubsetInPowerSet DEF Cases!KOneInPowerSet, Cases!K1, Cases!P

THEOREM KTwoInPowerSet == Cases!KTwoInPowerSet
  BY KSubsetInPowerSet DEF Cases!KTwoInPowerSet, Cases!K2, Cases!P

THEOREM KThreeInPowerSet == Cases!KThreeInPowerSet
  BY KSubsetInPowerSet DEF Cases!KThreeInPowerSet, Cases!K3, Cases!P

THEOREM KZeroInPowerSet == Cases!KZeroInPowerSet
  BY KSubsetInPowerSet DEF Cases!KZeroInPowerSet, Cases!K0, Cases!P

THEOREM KZeroInAnyPowerSet ==
  ASSUME NEW S, NEW T, IsFiniteSet(S)
  PROVE  kSubset(0, S) \subseteq SUBSET T
  <1> SUFFICES ASSUME NEW s \in kSubset(0, S)
               PROVE  s \subseteq T
    OBVIOUS
  <1>1. s \in SUBSET S /\ Cardinality(s) = 0
    BY DEF kSubset
  <1>2. IsFiniteSet(s)
    BY <1>1, FS_Subset
  <1>3. s = {}
    BY <1>1, <1>2, FS_EmptySet
  <1>4. QED BY <1>3

THEOREM KZeroInEmptyPowerSet == Cases!KZeroInEmptyPowerSet
  BY FS_Interval, KZeroInAnyPowerSet
     DEF Cases!KZeroInEmptyPowerSet, Cases!K0

THEOREM KZeroLargerInPowerSet == Cases!KZeroLargerInPowerSet
  BY FS_Interval, KZeroInAnyPowerSet
     DEF Cases!KZeroLargerInPowerSet, Cases!P

THEOREM EmptyInAnyPowerSet ==
  ASSUME NEW T
  PROVE  {} \subseteq SUBSET T
  OBVIOUS

THEOREM KSubsetTooLargeInSmallerPowerSet ==
  Cases!KSubsetTooLargeInSmallerPowerSet
  BY KSubsetTooLargeEmpty, EmptyInAnyPowerSet
     DEF Cases!KSubsetTooLargeInSmallerPowerSet,
         Cases!KSubsetTooLargeEmpty

THEOREM KSubsetNegativeInSmallerPowerSet ==
  Cases!KSubsetNegativeInSmallerPowerSet
  BY KSubsetNegativeEmpty, EmptyInAnyPowerSet
     DEF Cases!KSubsetNegativeInSmallerPowerSet,
         Cases!KSubsetNegativeEmpty

THEOREM PowerSetNotInKOne == Cases!PowerSetNotInKOne
  BY KOneThree, PowerSetThree
     DEF Cases!PowerSetNotInKOne, Cases!P

THEOREM PowerSetNotInKTwo == Cases!PowerSetNotInKTwo
  BY EmptyNotInKTwo, PowerSetThree
     DEF Cases!PowerSetNotInKTwo, Cases!EmptyNotInKTwo

THEOREM PowerSetNotInKThree == Cases!PowerSetNotInKThree
  BY KThreeThree, PowerSetThree
     DEF Cases!PowerSetNotInKThree, Cases!P

THEOREM KOneNotInKTwo == Cases!KOneNotInKTwo
  <1>1. {1} \in Cases!K1 /\ {1} \notin Cases!K2
    BY KOneThree, KTwoThree
  <1>2. QED BY <1>1 DEF Cases!KOneNotInKTwo

THEOREM KTwoNotInKOne == Cases!KTwoNotInKOne
  BY KOneThree, KTwoThree DEF Cases!KTwoNotInKOne

THEOREM KOneNotInKThree == Cases!KOneNotInKThree
  BY KOneThree, KThreeThree DEF Cases!KOneNotInKThree

THEOREM KThreeNotInKOne == Cases!KThreeNotInKOne
  BY KOneThree, KThreeThree DEF Cases!KThreeNotInKOne

THEOREM KTwoNotInKThree == Cases!KTwoNotInKThree
  BY KTwoThree, KThreeThree DEF Cases!KTwoNotInKThree

THEOREM KThreeNotInKTwo == Cases!KThreeNotInKTwo
  BY KTwoThree, KThreeThree DEF Cases!KThreeNotInKTwo

THEOREM KOneInEnumOne == Cases!KOneInEnumOne
  BY KOneThree DEF Cases!KOneInEnumOne, Cases!E1

THEOREM EnumOneInKOne == Cases!EnumOneInKOne
  BY KOneThree DEF Cases!EnumOneInKOne, Cases!E1

THEOREM KTwoInEnumTwo == Cases!KTwoInEnumTwo
  BY KTwoThree DEF Cases!KTwoInEnumTwo, Cases!E2

THEOREM EnumTwoInKTwo == Cases!EnumTwoInKTwo
  BY KTwoThree DEF Cases!EnumTwoInKTwo, Cases!E2

-----------------------------------------------------------------------------
\* Extensional equality and disequality across base sets and representations.

THEOREM KTwoOfFourDiffKTwoOfThree == Cases!KTwoOfFourDiffKTwoOfThree
  <1>1. {1, 4} \in kSubset(2, 1..4)
    <2>1. {1, 4} \subseteq 1..4
      OBVIOUS
    <2>2. Cardinality({1, 4}) = 2
      <3>1. IsFiniteSet({4}) /\ Cardinality({4}) = 1
        BY FS_Singleton
      <3>2. 1 \notin {4}
        OBVIOUS
      <3>3. QED BY <3>1, <3>2, FS_AddElement
    <2>3. QED BY <2>1, <2>2 DEF kSubset
  <1>2. {1, 4} \notin Cases!K2
    BY KTwoThree
  <1>3. QED BY <1>1, <1>2 DEF Cases!KTwoOfFourDiffKTwoOfThree

THEOREM KTwoOfThreeDiffKTwoOfFour == Cases!KTwoOfThreeDiffKTwoOfFour
  BY KTwoOfFourDiffKTwoOfThree
     DEF Cases!KTwoOfThreeDiffKTwoOfFour,
         Cases!KTwoOfFourDiffKTwoOfThree

THEOREM KZeroBaseIndependent == Cases!KZeroBaseIndependent
  <1>1. IsFiniteSet(1..4)
    BY FS_Interval
  <1>2. \A s \in SUBSET (1..4) : Cardinality(s) = 0 <=> s = {}
    <2>1. SUFFICES ASSUME NEW s \in SUBSET (1..4)
                     PROVE Cardinality(s) = 0 <=> s = {}
      OBVIOUS
    <2>2. IsFiniteSet(s)
      BY <1>1, FS_Subset
    <2>3. QED BY <2>2, FS_EmptySet
  <1>3. kSubset(0, 1..4) = {{}}
    BY <1>2 DEF kSubset
  <1>4. QED BY <1>3, KZeroThree DEF Cases!KZeroBaseIndependent

THEOREM KZeroEqEnum == Cases!KZeroEqEnum
  BY KZeroThree DEF Cases!KZeroEqEnum, Cases!E0

THEOREM EnumEqKZero == Cases!EnumEqKZero
  BY KZeroThree DEF Cases!EnumEqKZero, Cases!E0

THEOREM KOneEqEnum == Cases!KOneEqEnum
  BY KOneThree DEF Cases!KOneEqEnum, Cases!E1

THEOREM EnumEqKOne == Cases!EnumEqKOne
  BY KOneThree DEF Cases!EnumEqKOne, Cases!E1

THEOREM KTwoEqEnum == Cases!KTwoEqEnum
  BY KTwoThree DEF Cases!KTwoEqEnum, Cases!E2

THEOREM EnumEqKTwo == Cases!EnumEqKTwo
  BY KTwoThree DEF Cases!EnumEqKTwo, Cases!E2

THEOREM KZeroEqSym == Cases!KZeroEqSym
  BY KZeroThreeSym DEF Cases!KZeroEqSym

THEOREM KZeroEqSymRev == Cases!KZeroEqSymRev
  BY KZeroThreeSym DEF Cases!KZeroEqSymRev

THEOREM KOneEqSym == Cases!KOneEqSym
  BY KOneThreeSym DEF Cases!KOneEqSym

THEOREM KOneEqSymRev == Cases!KOneEqSymRev
  BY KOneThreeSym DEF Cases!KOneEqSymRev

THEOREM KTwoEqSym == Cases!KTwoEqSym
  BY KTwoThreeSym DEF Cases!KTwoEqSym

THEOREM KTwoEqSymRev == Cases!KTwoEqSymRev
  BY KTwoThreeSym DEF Cases!KTwoEqSymRev

THEOREM KThreeEqSym == Cases!KThreeEqSym
  BY KThreeThreeSym DEF Cases!KThreeEqSym

THEOREM KThreeEqSymRev == Cases!KThreeEqSymRev
  BY KThreeThreeSym DEF Cases!KThreeEqSymRev

LEMMA KTwoFourDefinition == Cases!K24 = Cases!D24
  BY DEF Cases!K24, Cases!D24, kSubset

LEMMA KTwoFourSymDefinition == Cases!K24Sym = Cases!D24
  BY DEF Cases!K24Sym, Cases!D24, kSubset

LEMMA KThreeFourDefinition == Cases!K34 = Cases!D34
  BY DEF Cases!K34, Cases!D34, kSubset

LEMMA KThreeFourSymDefinition == Cases!K34Sym = Cases!D34
  BY DEF Cases!K34Sym, Cases!D34, kSubset

LEMMA KThreeFiveDefinition == Cases!K35 = Cases!D35
  BY DEF Cases!K35, Cases!D35, kSubset

LEMMA KThreeFiveSymDefinition == Cases!K35Sym = Cases!D35
  BY DEF Cases!K35Sym, Cases!D35, kSubset

THEOREM KTwoFourInDefinition == Cases!KTwoFourInDefinition
  BY KTwoFourDefinition DEF Cases!KTwoFourInDefinition

THEOREM DefinitionInKTwoFour == Cases!DefinitionInKTwoFour
  BY KTwoFourDefinition DEF Cases!DefinitionInKTwoFour

THEOREM KTwoFourSymInDefinition == Cases!KTwoFourSymInDefinition
  BY KTwoFourSymDefinition DEF Cases!KTwoFourSymInDefinition

THEOREM DefinitionInKTwoFourSym == Cases!DefinitionInKTwoFourSym
  BY KTwoFourSymDefinition DEF Cases!DefinitionInKTwoFourSym

THEOREM KThreeFourInDefinition == Cases!KThreeFourInDefinition
  BY KThreeFourDefinition DEF Cases!KThreeFourInDefinition

THEOREM DefinitionInKThreeFour == Cases!DefinitionInKThreeFour
  BY KThreeFourDefinition DEF Cases!DefinitionInKThreeFour

THEOREM KThreeFourSymInDefinition == Cases!KThreeFourSymInDefinition
  BY KThreeFourSymDefinition DEF Cases!KThreeFourSymInDefinition

THEOREM DefinitionInKThreeFourSym == Cases!DefinitionInKThreeFourSym
  BY KThreeFourSymDefinition DEF Cases!DefinitionInKThreeFourSym

THEOREM KThreeFiveInDefinition == Cases!KThreeFiveInDefinition
  BY KThreeFiveDefinition DEF Cases!KThreeFiveInDefinition

THEOREM DefinitionInKThreeFive == Cases!DefinitionInKThreeFive
  BY KThreeFiveDefinition DEF Cases!DefinitionInKThreeFive

THEOREM KThreeFiveSymInDefinition == Cases!KThreeFiveSymInDefinition
  BY KThreeFiveSymDefinition DEF Cases!KThreeFiveSymInDefinition

THEOREM DefinitionInKThreeFiveSym == Cases!DefinitionInKThreeFiveSym
  BY KThreeFiveSymDefinition DEF Cases!DefinitionInKThreeFiveSym

THEOREM KTwoFourEqDefinition == Cases!KTwoFourEqDefinition
  BY KTwoFourDefinition DEF Cases!KTwoFourEqDefinition

THEOREM DefinitionEqKTwoFour == Cases!DefinitionEqKTwoFour
  BY KTwoFourDefinition DEF Cases!DefinitionEqKTwoFour

THEOREM KTwoFourSymEqDefinition == Cases!KTwoFourSymEqDefinition
  BY KTwoFourSymDefinition DEF Cases!KTwoFourSymEqDefinition

THEOREM DefinitionEqKTwoFourSym == Cases!DefinitionEqKTwoFourSym
  BY KTwoFourSymDefinition DEF Cases!DefinitionEqKTwoFourSym

THEOREM KThreeFourEqDefinition == Cases!KThreeFourEqDefinition
  BY KThreeFourDefinition DEF Cases!KThreeFourEqDefinition

THEOREM DefinitionEqKThreeFour == Cases!DefinitionEqKThreeFour
  BY KThreeFourDefinition DEF Cases!DefinitionEqKThreeFour

THEOREM KThreeFourSymEqDefinition == Cases!KThreeFourSymEqDefinition
  BY KThreeFourSymDefinition DEF Cases!KThreeFourSymEqDefinition

THEOREM DefinitionEqKThreeFourSym == Cases!DefinitionEqKThreeFourSym
  BY KThreeFourSymDefinition DEF Cases!DefinitionEqKThreeFourSym

THEOREM KThreeFiveEqDefinition == Cases!KThreeFiveEqDefinition
  BY KThreeFiveDefinition DEF Cases!KThreeFiveEqDefinition

THEOREM DefinitionEqKThreeFive == Cases!DefinitionEqKThreeFive
  BY KThreeFiveDefinition DEF Cases!DefinitionEqKThreeFive

THEOREM KThreeFiveSymEqDefinition == Cases!KThreeFiveSymEqDefinition
  BY KThreeFiveSymDefinition DEF Cases!KThreeFiveSymEqDefinition

THEOREM DefinitionEqKThreeFiveSym == Cases!DefinitionEqKThreeFiveSym
  BY KThreeFiveSymDefinition DEF Cases!DefinitionEqKThreeFiveSym

THEOREM KSubsetNormalizedBaseEqDefinition ==
  Cases!KSubsetNormalizedBaseEqDefinition
  BY DEF Cases!KSubsetNormalizedBaseEqDefinition, kSubset

THEOREM KSubsetNormalizedBaseBoundsEmpty ==
  Cases!KSubsetNormalizedBaseBoundsEmpty
  <1>1. IsFiniteSet({"a", "b", "c", "c"})
          /\ Cardinality({"a", "b", "c", "c"}) = 3
    <2>1. IsFiniteSet({"c"}) /\ Cardinality({"c"}) = 1
      BY FS_Singleton
    <2>2. "b" \notin {"c"}
      OBVIOUS
    <2>3. IsFiniteSet({"c"} \cup {"b"})
            /\ Cardinality({"c"} \cup {"b"}) = 2
      BY <2>1, <2>2, FS_AddElement
    <2>4. "a" \notin {"b", "c"}
      OBVIOUS
    <2>5. QED BY <2>3, <2>4, FS_AddElement
  <1>2. kSubset(-1, {"a", "b", "c", "c"}) = {}
    <2> SUFFICES ASSUME NEW s \in kSubset(-1, {"a", "b", "c", "c"})
                 PROVE  FALSE
      OBVIOUS
    <2>1. s \in SUBSET {"a", "b", "c", "c"} /\ Cardinality(s) = -1
      BY DEF kSubset
    <2>2. IsFiniteSet(s)
      BY <1>1, <2>1, FS_Subset
    <2>3. Cardinality(s) \in Nat
      BY <2>2, FS_CardinalityType
    <2>4. QED BY <2>1, <2>3
  <1>3. kSubset(4, {"a", "b", "c", "c"}) = {}
    <2> SUFFICES ASSUME NEW s \in kSubset(4, {"a", "b", "c", "c"})
                 PROVE  FALSE
      OBVIOUS
    <2>1. s \in SUBSET {"a", "b", "c", "c"} /\ Cardinality(s) = 4
      BY DEF kSubset
    <2>2. Cardinality(s) <= Cardinality({"a", "b", "c", "c"})
      BY <1>1, <2>1, FS_Subset
    <2>3. QED BY <1>1, <2>1, <2>2
  <1>4. QED BY <1>2, <1>3
    DEF Cases!KSubsetNormalizedBaseBoundsEmpty

THEOREM KSubsetFullFinite ==
  ASSUME NEW S, IsFiniteSet(S)
  PROVE  kSubset(Cardinality(S), S) = {S}
  <1>1. \A s \in SUBSET S :
          Cardinality(s) = Cardinality(S) => s = S
    BY FS_Subset
  <1>2. S \in SUBSET S
    OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF kSubset

THEOREM KSubsetFullLargeBase == Cases!KSubsetFullLargeBase
  BY KSubsetFullFinite, FS_Interval DEF Cases!KSubsetFullLargeBase

THEOREM EmptyNotInKOneThree == Cases!EmptyNotInKOneThree
  BY FS_EmptySet DEF Cases!EmptyNotInKOneThree, kSubset

THEOREM KSubsetMembershipAgreesWithDefinition ==
  Cases!KSubsetMembershipAgreesWithDefinition
  BY DEF Cases!KSubsetMembershipAgreesWithDefinition, kSubset

THEOREM RcdSetOfKSubsetReflexive == Cases!RcdSetOfKSubsetReflexive
  BY DEF Cases!RcdSetOfKSubsetReflexive

-----------------------------------------------------------------------------
\* Pairwise disequality among k-subsets and between them and the base power set.

THEOREM KOneDiffKTwo == Cases!KOneDiffKTwo
  <1>1. {1} \in Cases!K1 /\ {1} \notin Cases!K2
    BY KOneThree, KTwoThree
  <1>2. QED BY <1>1 DEF Cases!KOneDiffKTwo

THEOREM KTwoDiffKOne == Cases!KTwoDiffKOne
  BY KOneDiffKTwo DEF Cases!KTwoDiffKOne, Cases!KOneDiffKTwo

THEOREM KOneDiffKThree == Cases!KOneDiffKThree
  <1>1. {1} \in Cases!K1 /\ {1} \notin Cases!K3
    BY KOneThree, KThreeThree
  <1>2. QED BY <1>1 DEF Cases!KOneDiffKThree

THEOREM KThreeDiffKOne == Cases!KThreeDiffKOne
  BY KOneDiffKThree DEF Cases!KThreeDiffKOne, Cases!KOneDiffKThree

THEOREM KTwoDiffKThree == Cases!KTwoDiffKThree
  <1>1. {1, 2} \in Cases!K2 /\ {1, 2} \notin Cases!K3
    BY KTwoThree, KThreeThree
  <1>2. QED BY <1>1 DEF Cases!KTwoDiffKThree

THEOREM KThreeDiffKTwo == Cases!KThreeDiffKTwo
  BY KTwoDiffKThree DEF Cases!KThreeDiffKTwo, Cases!KTwoDiffKThree

THEOREM KOneDiffPowerSet == Cases!KOneDiffPowerSet
  BY KOneThree, PowerSetThree DEF Cases!KOneDiffPowerSet

THEOREM KTwoDiffPowerSet == Cases!KTwoDiffPowerSet
  <1>1. {} \in Cases!P /\ {} \notin Cases!K2
    BY PowerSetThree, KTwoThree
  <1>2. QED BY <1>1 DEF Cases!KTwoDiffPowerSet

THEOREM KThreeDiffPowerSet == Cases!KThreeDiffPowerSet
  <1>1. {} \in Cases!P /\ {} \notin Cases!K3
    BY PowerSetThree, KThreeThree
  <1>2. QED BY <1>1 DEF Cases!KThreeDiffPowerSet

THEOREM PowerSetDiffKOne == Cases!PowerSetDiffKOne
  BY KOneDiffPowerSet
     DEF Cases!PowerSetDiffKOne, Cases!KOneDiffPowerSet

THEOREM PowerSetDiffKTwo == Cases!PowerSetDiffKTwo
  BY KTwoDiffPowerSet DEF Cases!PowerSetDiffKTwo, Cases!KTwoDiffPowerSet

THEOREM PowerSetDiffKThree == Cases!PowerSetDiffKThree
  BY KThreeDiffPowerSet
     DEF Cases!PowerSetDiffKThree, Cases!KThreeDiffPowerSet

THEOREM KOneSingletonDiff == Cases!KOneSingletonDiff
  BY KOneDiffKTwo DEF Cases!KOneSingletonDiff, Cases!KOneDiffKTwo

THEOREM KOneSingletonDiffRev == Cases!KOneSingletonDiffRev
  BY KOneSingletonDiff
     DEF Cases!KOneSingletonDiffRev, Cases!KOneSingletonDiff

THEOREM KTwoNotInPowerSetSingleton == Cases!KTwoNotInPowerSetSingleton
  BY KTwoDiffPowerSet
     DEF Cases!KTwoNotInPowerSetSingleton, Cases!KTwoDiffPowerSet

-----------------------------------------------------------------------------
\* Cardinalities of finite sets containing k-subset values.

LEMMA TwoDistinctCardinality ==
  ASSUME NEW x, NEW y, x # y
  PROVE  Cardinality({x, y}) = 2
  <1>1. IsFiniteSet({y}) /\ Cardinality({y}) = 1
    BY FS_Singleton
  <1>2. x \notin {y}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2, FS_AddElement

THEOREM CardPairKZeroNatKOneNat == Cases!CardPairKZeroNatKOneNat
  BY KZeroNatDiffKOneNat, TwoDistinctCardinality
     DEF Cases!CardPairKZeroNatKOneNat

THEOREM CardPairKOneNatKZeroNat == Cases!CardPairKOneNatKZeroNat
  BY CardPairKZeroNatKOneNat
     DEF Cases!CardPairKZeroNatKOneNat, Cases!CardPairKOneNatKZeroNat

THEOREM CardPairKOneKTwo == Cases!CardPairKOneKTwo
  <1>1. IsFiniteSet({Cases!K2}) /\ Cardinality({Cases!K2}) = 1
    BY FS_Singleton
  <1>2. Cases!K1 \notin {Cases!K2}
    BY KOneDiffKTwo DEF Cases!KOneDiffKTwo
  <1>3. Cardinality({Cases!K2} \cup {Cases!K1}) = 2
    BY <1>1, <1>2, FS_AddElement
  <1>4. QED BY <1>3 DEF Cases!CardPairKOneKTwo

THEOREM CardPairKTwoKOne == Cases!CardPairKTwoKOne
  BY CardPairKOneKTwo
     DEF Cases!CardPairKTwoKOne, Cases!CardPairKOneKTwo

THEOREM CardPairKOneKThree == Cases!CardPairKOneKThree
  BY TwoDistinctCardinality, KOneDiffKThree
     DEF Cases!CardPairKOneKThree, Cases!KOneDiffKThree

THEOREM CardPairKThreeKOne == Cases!CardPairKThreeKOne
  BY CardPairKOneKThree
     DEF Cases!CardPairKThreeKOne, Cases!CardPairKOneKThree

THEOREM CardPairKTwoKThree == Cases!CardPairKTwoKThree
  BY TwoDistinctCardinality, KTwoDiffKThree
     DEF Cases!CardPairKTwoKThree, Cases!KTwoDiffKThree

THEOREM CardPairKThreeKTwo == Cases!CardPairKThreeKTwo
  BY CardPairKTwoKThree
     DEF Cases!CardPairKThreeKTwo, Cases!CardPairKTwoKThree

LEMMA KTwoEightDiffKOneFive == Cases!K28 # Cases!K15
  <1>1. {1, 2} \in Cases!K28
    BY CardinalitiesThree DEF Cases!K28, kSubset
  <1>2. {1, 2} \notin Cases!K15
    BY CardinalitiesThree DEF Cases!K15, kSubset
  <1>3. QED BY <1>1, <1>2

THEOREM CardPairKTwoEightKOneFive ==
  Cases!CardPairKTwoEightKOneFive
  BY TwoDistinctCardinality, KTwoEightDiffKOneFive
     DEF Cases!CardPairKTwoEightKOneFive

THEOREM CardPairKOneFiveKTwoEight ==
  Cases!CardPairKOneFiveKTwoEight
  BY CardPairKTwoEightKOneFive
     DEF Cases!CardPairKOneFiveKTwoEight,
         Cases!CardPairKTwoEightKOneFive

LEMMA KThreeSixDiffKOneTwenty == Cases!K36 # Cases!K120
  <1>1. {1} \notin Cases!K36
    BY FS_Singleton DEF Cases!K36, kSubset
  <1>2. {1} \in Cases!K120
    BY FS_Singleton DEF Cases!K120, kSubset
  <1>3. QED BY <1>1, <1>2

THEOREM CardPairKThreeSixKOneTwenty ==
  Cases!CardPairKThreeSixKOneTwenty
  BY TwoDistinctCardinality, KThreeSixDiffKOneTwenty
     DEF Cases!CardPairKThreeSixKOneTwenty

THEOREM CardPairKOneTwentyKThreeSix ==
  Cases!CardPairKOneTwentyKThreeSix
  BY CardPairKThreeSixKOneTwenty
     DEF Cases!CardPairKThreeSixKOneTwenty,
         Cases!CardPairKOneTwentyKThreeSix

THEOREM CardTripleKs == Cases!CardTripleKs
  <1>1. IsFiniteSet({Cases!K2, Cases!K3})
        /\ Cardinality({Cases!K2, Cases!K3}) = 2
    <2>1. IsFiniteSet({Cases!K3}) /\ Cardinality({Cases!K3}) = 1
      BY FS_Singleton
    <2>2. Cases!K2 \notin {Cases!K3}
      BY KTwoDiffKThree DEF Cases!KTwoDiffKThree
    <2>3. QED BY <2>1, <2>2, FS_AddElement
  <1>2. Cases!K1 \notin {Cases!K2, Cases!K3}
    BY KOneDiffKTwo, KOneDiffKThree
       DEF Cases!KOneDiffKTwo, Cases!KOneDiffKThree
  <1>3. Cardinality({Cases!K2, Cases!K3} \cup {Cases!K1}) = 3
    BY <1>1, <1>2, FS_AddElement
  <1>4. QED BY <1>3 DEF Cases!CardTripleKs

THEOREM CardTripleKsRev == Cases!CardTripleKsRev
  BY CardTripleKs DEF Cases!CardTripleKsRev, Cases!CardTripleKs

THEOREM CardPairKTwoPowerSet == Cases!CardPairKTwoPowerSet
  <1>1. IsFiniteSet({Cases!P}) /\ Cardinality({Cases!P}) = 1
    BY FS_Singleton
  <1>2. Cases!K2 \notin {Cases!P}
    BY KTwoDiffPowerSet DEF Cases!KTwoDiffPowerSet
  <1>3. Cardinality({Cases!P} \cup {Cases!K2}) = 2
    BY <1>1, <1>2, FS_AddElement
  <1>4. QED BY <1>3 DEF Cases!CardPairKTwoPowerSet

THEOREM CardPairPowerSetKTwo == Cases!CardPairPowerSetKTwo
  BY CardPairKTwoPowerSet
     DEF Cases!CardPairPowerSetKTwo, Cases!CardPairKTwoPowerSet

THEOREM CardTripleKsPowerSet == Cases!CardTripleKsPowerSet
  <1>1. IsFiniteSet({Cases!K2, Cases!P})
        /\ Cardinality({Cases!K2, Cases!P}) = 2
    <2>1. IsFiniteSet({Cases!P}) /\ Cardinality({Cases!P}) = 1
      BY FS_Singleton
    <2>2. Cases!K2 \notin {Cases!P}
      BY KTwoDiffPowerSet DEF Cases!KTwoDiffPowerSet
    <2>3. QED BY <2>1, <2>2, FS_AddElement
  <1>2. Cases!K1 \notin {Cases!K2, Cases!P}
    <2>1. {1} \in Cases!K1 /\ {1} \notin Cases!K2
      BY KOneThree, KTwoThree
    <2>2. {} \in Cases!P /\ {} \notin Cases!K1
      BY PowerSetThree, KOneThree
    <2>3. QED BY <2>1, <2>2
  <1>3. Cardinality({Cases!K2, Cases!P} \cup {Cases!K1}) = 3
    BY <1>1, <1>2, FS_AddElement
  <1>4. QED BY <1>3 DEF Cases!CardTripleKsPowerSet

THEOREM CardTriplePowerSetKs == Cases!CardTriplePowerSetKs
  BY CardTripleKsPowerSet
     DEF Cases!CardTriplePowerSetKs, Cases!CardTripleKsPowerSet

\* A k-subset and its extensionally equal representation coalesce under set
\* construction, independently of source order.

THEOREM CardKZeroWithEnum == Cases!CardKZeroWithEnum
  <1>1. {Cases!K0, Cases!E0} = {Cases!K0}
    BY KZeroThree DEF Cases!E0
  <1>2. QED BY <1>1, FS_Singleton DEF Cases!CardKZeroWithEnum

THEOREM CardEnumWithKZero == Cases!CardEnumWithKZero
  BY CardKZeroWithEnum
     DEF Cases!CardEnumWithKZero, Cases!CardKZeroWithEnum

THEOREM CardKOneWithEnum == Cases!CardKOneWithEnum
  <1>1. {Cases!K1, Cases!E1} = {Cases!K1}
    BY KOneThree DEF Cases!E1
  <1>2. QED BY <1>1, FS_Singleton DEF Cases!CardKOneWithEnum

THEOREM CardEnumWithKOne == Cases!CardEnumWithKOne
  <1>1. {Cases!E1, Cases!K1} = {Cases!K1}
    BY KOneThree DEF Cases!E1
  <1>2. QED BY <1>1, FS_Singleton DEF Cases!CardEnumWithKOne

THEOREM CardKTwoWithEnum == Cases!CardKTwoWithEnum
  <1>1. {Cases!K2, Cases!E2} = {Cases!K2}
    BY KTwoThree DEF Cases!E2
  <1>2. QED BY <1>1, FS_Singleton DEF Cases!CardKTwoWithEnum

THEOREM CardEnumWithKTwo == Cases!CardEnumWithKTwo
  BY CardKTwoWithEnum
     DEF Cases!CardEnumWithKTwo, Cases!CardKTwoWithEnum

THEOREM CardKZeroWithSym == Cases!CardKZeroWithSym
  BY KZeroThreeSym, FS_Singleton DEF Cases!CardKZeroWithSym

THEOREM CardKZeroWithSymRev == Cases!CardKZeroWithSymRev
  BY CardKZeroWithSym
     DEF Cases!CardKZeroWithSymRev, Cases!CardKZeroWithSym

THEOREM CardKOneWithSym == Cases!CardKOneWithSym
  BY KOneThreeSym, FS_Singleton DEF Cases!CardKOneWithSym

THEOREM CardKOneWithSymRev == Cases!CardKOneWithSymRev
  BY CardKOneWithSym
     DEF Cases!CardKOneWithSymRev, Cases!CardKOneWithSym

THEOREM CardKTwoWithSym == Cases!CardKTwoWithSym
  BY KTwoThreeSym, FS_Singleton DEF Cases!CardKTwoWithSym

THEOREM CardKTwoWithSymRev == Cases!CardKTwoWithSymRev
  BY CardKTwoWithSym
     DEF Cases!CardKTwoWithSymRev, Cases!CardKTwoWithSym

THEOREM CardKThreeWithSym == Cases!CardKThreeWithSym
  BY KThreeThreeSym, FS_Singleton DEF Cases!CardKThreeWithSym

THEOREM CardKThreeWithSymRev == Cases!CardKThreeWithSymRev
  BY CardKThreeWithSym
     DEF Cases!CardKThreeWithSymRev, Cases!CardKThreeWithSym

THEOREM CardKTwoFourWithDefinition == Cases!CardKTwoFourWithDefinition
  <1>1. {Cases!K24, Cases!D24} = {Cases!K24}
    BY KTwoFourDefinition
  <1>2. QED BY <1>1, FS_Singleton
         DEF Cases!CardKTwoFourWithDefinition

THEOREM CardDefinitionWithKTwoFour == Cases!CardDefinitionWithKTwoFour
  <1>1. {Cases!D24, Cases!K24} = {Cases!K24}
    BY KTwoFourDefinition
  <1>2. QED BY <1>1, FS_Singleton
         DEF Cases!CardDefinitionWithKTwoFour

THEOREM CardKTwoFourSymWithDefinition ==
  Cases!CardKTwoFourSymWithDefinition
  BY KTwoFourSymDefinition, FS_Singleton
     DEF Cases!CardKTwoFourSymWithDefinition

THEOREM CardDefinitionWithKTwoFourSym ==
  Cases!CardDefinitionWithKTwoFourSym
  BY CardKTwoFourSymWithDefinition
     DEF Cases!CardDefinitionWithKTwoFourSym,
         Cases!CardKTwoFourSymWithDefinition

THEOREM CardKThreeFourWithDefinition ==
  Cases!CardKThreeFourWithDefinition
  BY KThreeFourDefinition, FS_Singleton
     DEF Cases!CardKThreeFourWithDefinition

THEOREM CardDefinitionWithKThreeFour ==
  Cases!CardDefinitionWithKThreeFour
  BY CardKThreeFourWithDefinition
     DEF Cases!CardDefinitionWithKThreeFour,
         Cases!CardKThreeFourWithDefinition

THEOREM CardKThreeFourSymWithDefinition ==
  Cases!CardKThreeFourSymWithDefinition
  BY KThreeFourSymDefinition, FS_Singleton
     DEF Cases!CardKThreeFourSymWithDefinition

THEOREM CardDefinitionWithKThreeFourSym ==
  Cases!CardDefinitionWithKThreeFourSym
  BY CardKThreeFourSymWithDefinition
     DEF Cases!CardDefinitionWithKThreeFourSym,
         Cases!CardKThreeFourSymWithDefinition

THEOREM CardKThreeFiveWithDefinition ==
  Cases!CardKThreeFiveWithDefinition
  BY KThreeFiveDefinition, FS_Singleton
     DEF Cases!CardKThreeFiveWithDefinition

THEOREM CardDefinitionWithKThreeFive ==
  Cases!CardDefinitionWithKThreeFive
  BY CardKThreeFiveWithDefinition
     DEF Cases!CardDefinitionWithKThreeFive,
         Cases!CardKThreeFiveWithDefinition

THEOREM CardKThreeFiveSymWithDefinition ==
  Cases!CardKThreeFiveSymWithDefinition
  BY KThreeFiveSymDefinition, FS_Singleton
     DEF Cases!CardKThreeFiveSymWithDefinition

THEOREM CardDefinitionWithKThreeFiveSym ==
  Cases!CardDefinitionWithKThreeFiveSym
  BY CardKThreeFiveSymWithDefinition
     DEF Cases!CardDefinitionWithKThreeFiveSym,
         Cases!CardKThreeFiveSymWithDefinition

THEOREM CardKSubsetTooLargeWithEmpty ==
  Cases!CardKSubsetTooLargeWithEmpty
  BY KSubsetTooLargeEmpty, FS_Singleton
     DEF Cases!CardKSubsetTooLargeWithEmpty, Cases!KSubsetTooLargeEmpty

THEOREM CardEmptyWithKSubsetTooLarge ==
  Cases!CardEmptyWithKSubsetTooLarge
  BY CardKSubsetTooLargeWithEmpty
     DEF Cases!CardEmptyWithKSubsetTooLarge,
         Cases!CardKSubsetTooLargeWithEmpty

THEOREM CardKSubsetNegativeWithEmpty ==
  Cases!CardKSubsetNegativeWithEmpty
  BY KSubsetNegativeEmpty, FS_Singleton
     DEF Cases!CardKSubsetNegativeWithEmpty, Cases!KSubsetNegativeEmpty

THEOREM CardEmptyWithKSubsetNegative ==
  Cases!CardEmptyWithKSubsetNegative
  BY CardKSubsetNegativeWithEmpty
     DEF Cases!CardEmptyWithKSubsetNegative,
         Cases!CardKSubsetNegativeWithEmpty

THEOREM CardKsWithEnumOne == Cases!CardKsWithEnumOne
  <1>1. {Cases!K1, Cases!K2, Cases!E1} = {Cases!K1, Cases!K2}
    BY KOneThree DEF Cases!E1
  <1>2. QED BY <1>1, CardPairKOneKTwo
         DEF Cases!CardKsWithEnumOne, Cases!CardPairKOneKTwo

THEOREM CardKsWithEnumOneRev == Cases!CardKsWithEnumOneRev
  BY CardKsWithEnumOne
     DEF Cases!CardKsWithEnumOneRev, Cases!CardKsWithEnumOne

THEOREM CardKsWithEnumTwo == Cases!CardKsWithEnumTwo
  <1>1. {Cases!K1, Cases!E2, Cases!K2} = {Cases!K1, Cases!K2}
    BY KTwoThree DEF Cases!E2
  <1>2. QED BY <1>1, CardPairKOneKTwo
         DEF Cases!CardKsWithEnumTwo, Cases!CardPairKOneKTwo

THEOREM CardKsWithEnumTwoRev == Cases!CardKsWithEnumTwoRev
  BY CardKsWithEnumTwo
     DEF Cases!CardKsWithEnumTwoRev, Cases!CardKsWithEnumTwo

THEOREM CardEnumsWithKs == Cases!CardEnumsWithKs
  <1>1. {Cases!E2, Cases!E1, Cases!K2, Cases!K1} = {Cases!K1, Cases!K2}
    BY KOneThree, KTwoThree DEF Cases!E1, Cases!E2
  <1>2. QED BY <1>1, CardPairKOneKTwo
         DEF Cases!CardEnumsWithKs, Cases!CardPairKOneKTwo

THEOREM CardKsWithEnums == Cases!CardKsWithEnums
  <1>1. {Cases!K1, Cases!K2, Cases!E1, Cases!E2} = {Cases!K1, Cases!K2}
    BY KOneThree, KTwoThree DEF Cases!E1, Cases!E2
  <1>2. QED BY <1>1, CardPairKOneKTwo
         DEF Cases!CardKsWithEnums, Cases!CardPairKOneKTwo

THEOREM CardTripleKsWithEnums == Cases!CardTripleKsWithEnums
  <1>1. {Cases!K1, Cases!K2, Cases!K3, Cases!E1, Cases!E2}
          = {Cases!K1, Cases!K2, Cases!K3}
    BY KOneThree, KTwoThree DEF Cases!E1, Cases!E2
  <1>2. QED BY <1>1, CardTripleKs
         DEF Cases!CardTripleKsWithEnums, Cases!CardTripleKs

THEOREM CardTripleKsWithEnumsRev == Cases!CardTripleKsWithEnumsRev
  BY CardTripleKsWithEnums
     DEF Cases!CardTripleKsWithEnumsRev, Cases!CardTripleKsWithEnums

-----------------------------------------------------------------------------
\* The instance substitutes the identity for TLCFP. These obligations reduce
\* fingerprint equality to the extensional equality required of any function.

THEOREM FPKOneEqEnum == Cases!FPKOneEqEnum
  BY KOneThree DEF Cases!FPKOneEqEnum, Cases!E1

THEOREM FPKTwoEqEnum == Cases!FPKTwoEqEnum
  BY KTwoThree DEF Cases!FPKTwoEqEnum, Cases!E2

THEOREM FPKZeroEqSym == Cases!FPKZeroEqSym
  BY KZeroThreeSym DEF Cases!FPKZeroEqSym

THEOREM FPKOneEqSym == Cases!FPKOneEqSym
  BY KOneThreeSym DEF Cases!FPKOneEqSym

THEOREM FPKTwoEqSym == Cases!FPKTwoEqSym
  BY KTwoThreeSym DEF Cases!FPKTwoEqSym

THEOREM FPKThreeEqSym == Cases!FPKThreeEqSym
  BY KThreeThreeSym DEF Cases!FPKThreeEqSym

THEOREM FPKOneDiffKTwo == Cases!FPKOneDiffKTwo
  BY KOneDiffKTwo DEF Cases!FPKOneDiffKTwo, Cases!KOneDiffKTwo

THEOREM FPKSubsetTooLargeEqEmpty == Cases!FPKSubsetTooLargeEqEmpty
  BY KSubsetTooLargeEmpty
     DEF Cases!FPKSubsetTooLargeEqEmpty, Cases!KSubsetTooLargeEmpty

THEOREM FPKSubsetNegativeEqEmpty == Cases!FPKSubsetNegativeEqEmpty
  BY KSubsetNegativeEmpty
     DEF Cases!FPKSubsetNegativeEqEmpty, Cases!KSubsetNegativeEmpty

THEOREM FPKTwoFourEqDefinition == Cases!FPKTwoFourEqDefinition
  BY KTwoFourDefinition DEF Cases!FPKTwoFourEqDefinition

THEOREM FPKTwoFourSymEqDefinition == Cases!FPKTwoFourSymEqDefinition
  BY KTwoFourSymDefinition DEF Cases!FPKTwoFourSymEqDefinition

THEOREM FPKThreeFourEqDefinition == Cases!FPKThreeFourEqDefinition
  BY KThreeFourDefinition DEF Cases!FPKThreeFourEqDefinition

THEOREM FPKThreeFourSymEqDefinition ==
  Cases!FPKThreeFourSymEqDefinition
  BY KThreeFourSymDefinition DEF Cases!FPKThreeFourSymEqDefinition

THEOREM FPKThreeFiveEqDefinition == Cases!FPKThreeFiveEqDefinition
  BY KThreeFiveDefinition DEF Cases!FPKThreeFiveEqDefinition

THEOREM FPKThreeFiveSymEqDefinition ==
  Cases!FPKThreeFiveSymEqDefinition
  BY KThreeFiveSymDefinition DEF Cases!FPKThreeFiveSymEqDefinition

THEOREM FPPairKTwoEightKOneFiveOrderIndependent ==
  Cases!FPPairKTwoEightKOneFiveOrderIndependent
  BY DEF Cases!FPPairKTwoEightKOneFiveOrderIndependent

THEOREM FPPairKThreeSixKOneTwentyOrderIndependent ==
  Cases!FPPairKThreeSixKOneTwentyOrderIndependent
  BY DEF Cases!FPPairKThreeSixKOneTwentyOrderIndependent

THEOREM FPMixedEqEnums == Cases!FPMixedEqEnums
  BY KOneThree, KTwoThree
     DEF Cases!FPMixedEqEnums, Cases!E1, Cases!E2

THEOREM FPMixedEqEnumsRev == Cases!FPMixedEqEnumsRev
  BY KOneThree, KTwoThree
     DEF Cases!FPMixedEqEnumsRev, Cases!E1, Cases!E2

THEOREM FPMixedOrderIndependent == Cases!FPMixedOrderIndependent
  BY DEF Cases!FPMixedOrderIndependent

-----------------------------------------------------------------------------
\* Large finite bases whose k-subset families are not feasibly enumerable.
\* Exact binomial-coefficient cases remain unchecked by TLAPS because its
\* finite-set library provides no corresponding counting theorem.

THEOREM CardKSubsetMiddleLargeReflexive ==
  Cases!CardKSubsetMiddleLargeReflexive
  BY DEF Cases!CardKSubsetMiddleLargeReflexive

THEOREM KSubsetFinite ==
  ASSUME NEW k, NEW S, IsFiniteSet(S)
  PROVE  IsFiniteSet(kSubset(k, S))
  <1>1. IsFiniteSet(SUBSET S)
    BY FS_SUBSET
  <1>2. kSubset(k, S) \subseteq SUBSET S
    BY KSubsetInPowerSet
  <1>3. QED BY <1>1, <1>2, FS_Subset

THEOREM KSubsetLargeFinite == Cases!KSubsetLargeFinite
  BY KSubsetFinite, FS_Interval DEF Cases!KSubsetLargeFinite

THEOREM PairInKSubsetLarge == Cases!PairInKSubsetLarge
  <1>1. {1, 2} \subseteq 1..64
    OBVIOUS
  <1>2. Cardinality({1, 2}) = 2
    <2>1. IsFiniteSet({2}) /\ Cardinality({2}) = 1
      BY FS_Singleton
    <2>2. 1 \notin {2}
      OBVIOUS
    <2>3. QED BY <2>1, <2>2, FS_AddElement
  <1>3. QED BY <1>1, <1>2 DEF Cases!PairInKSubsetLarge, kSubset

LEMMA K31DiffK32Large ==
  kSubset(31, 1..64) # kSubset(32, 1..64)
  <1>1. 1..31 \subseteq 1..64
    OBVIOUS
  <1>2. Cardinality(1..31) = 31
    BY FS_Interval
  <1>3. 1..31 \in kSubset(31, 1..64)
    BY <1>1, <1>2 DEF kSubset
  <1>4. 1..31 \notin kSubset(32, 1..64)
    BY <1>2 DEF kSubset
  <1>5. QED BY <1>3, <1>4

THEOREM CardPairK31K32Large == Cases!CardPairK31K32Large
  BY K31DiffK32Large, TwoDistinctCardinality
     DEF Cases!CardPairK31K32Large

THEOREM CardPairK32K31Large == Cases!CardPairK32K31Large
  BY CardPairK31K32Large
     DEF Cases!CardPairK31K32Large, Cases!CardPairK32K31Large

LEMMA K31LargeDiffK2Small ==
  kSubset(31, 1..64) # kSubset(2, 1..10)
  <1>1. {1, 2} \in kSubset(2, 1..10)
    <2>1. {1, 2} \subseteq 1..10
      OBVIOUS
    <2>2. Cardinality({1, 2}) = 2
      <3>1. IsFiniteSet({2}) /\ Cardinality({2}) = 1
        BY FS_Singleton
      <3>2. 1 \notin {2}
        OBVIOUS
      <3>3. QED BY <3>1, <3>2, FS_AddElement
    <2>3. QED BY <2>1, <2>2 DEF kSubset
  <1>2. {1, 2} \notin kSubset(31, 1..64)
    BY <1>1 DEF kSubset
  <1>3. QED BY <1>1, <1>2

THEOREM CardPairK31LargeK2Small == Cases!CardPairK31LargeK2Small
  BY K31LargeDiffK2Small, TwoDistinctCardinality
     DEF Cases!CardPairK31LargeK2Small

THEOREM CardPairK2SmallK31Large == Cases!CardPairK2SmallK31Large
  BY CardPairK31LargeK2Small
     DEF Cases!CardPairK31LargeK2Small, Cases!CardPairK2SmallK31Large

THEOREM KSubsetLargeDiffPowerSet == Cases!KSubsetLargeDiffPowerSet
  <1>1. {} \in SUBSET (1..64) /\ {} \notin kSubset(2, 1..64)
    BY FS_EmptySet DEF kSubset
  <1>2. QED BY <1>1 DEF Cases!KSubsetLargeDiffPowerSet

THEOREM PowerSetLargeDiffKSubset == Cases!PowerSetLargeDiffKSubset
  BY KSubsetLargeDiffPowerSet
     DEF Cases!KSubsetLargeDiffPowerSet, Cases!PowerSetLargeDiffKSubset

THEOREM CardPairKSubsetPowerSetLarge ==
  Cases!CardPairKSubsetPowerSetLarge
  BY KSubsetLargeDiffPowerSet, TwoDistinctCardinality
     DEF Cases!CardPairKSubsetPowerSetLarge,
         Cases!KSubsetLargeDiffPowerSet

THEOREM CardPairPowerSetKSubsetLarge ==
  Cases!CardPairPowerSetKSubsetLarge
  BY CardPairKSubsetPowerSetLarge
     DEF Cases!CardPairKSubsetPowerSetLarge,
         Cases!CardPairPowerSetKSubsetLarge
=============================================================================
