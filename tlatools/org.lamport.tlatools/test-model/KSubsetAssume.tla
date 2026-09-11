------------------------------ MODULE KSubsetAssume --------------------------
\* TLC checks each ASSUME at startup. Cases instantiates KSubsetCases with
\* FiniteSetsExt!kSubset, whose Java override returns a KSubsetValue.
\* KSubsetTheorems proves the corresponding propositions from the TLA+
\* definition of kSubset. The final ToString assumptions specify TLC output
\* and therefore have no representation-independent counterparts.
\*
\* See https://github.com/tlaplus/tlaplus/issues/1415 and
\* https://github.com/tlaplus/tlaplus/issues/1424
EXTENDS FiniteSets, FiniteSetsExt, Integers, TLC, TLCExt

Cases == INSTANCE KSubsetCases

ASSUME Cases!CardKZero
ASSUME Cases!CardKOne
ASSUME Cases!CardKTwo
ASSUME Cases!CardKThree
ASSUME Cases!KTwoElementCardinality
ASSUME Cases!KSubsetTooLargeEmpty
ASSUME Cases!KSubsetNegativeEmpty
ASSUME Cases!CardKSubsetTooLarge
ASSUME Cases!CardKSubsetNegative
ASSUME Cases!EmptyBaseKZeroUnit
ASSUME Cases!EmptyBaseKOneEmpty
ASSUME Cases!EmptyEqKSubsetTooLarge
ASSUME Cases!EmptyEqKSubsetNegative
\* ASSUME Cases!KZeroNestedEnumeration \* TLC does not terminate

\* FiniteSetsExt eagerly enumerates Nat before constructing a KSubsetValue.
\* ASSUME Cases!CardKZeroNat                 \* TLC refuses
\* ASSUME Cases!CardKSubsetNegativeNat       \* TLC refuses
\* ASSUME Cases!KZeroNatFinite               \* TLC refuses
\* ASSUME Cases!KSubsetNegativeNatFinite     \* TLC refuses
\* ASSUME Cases!KOneNatInfinite              \* TLC refuses
\* These memberships do not require enumerating the infinite base.
\* ASSUME Cases!EmptyInKZeroNat                    \* FiniteSetsExt refuses
\* ASSUME Cases!EmptyNotInKSubsetNegativeNat       \* FiniteSetsExt refuses
\* ASSUME Cases!SingletonNotInKZeroNat             \* FiniteSetsExt refuses
\* ASSUME Cases!SingletonInKOneNat                 \* FiniteSetsExt refuses
\* ASSUME Cases!EmptyInKZeroString                 \* FiniteSetsExt refuses
\* ASSUME Cases!EmptyNotInKSubsetNegativeString    \* FiniteSetsExt refuses
\* Pin TLC's representation-independent answers for non-finite bases.
\* ASSUME Cases!KZeroNatEqEnum                     \* FiniteSetsExt refuses
\* ASSUME Cases!KSubsetNegativeNatEmpty            \* FiniteSetsExt refuses
\* ASSUME Cases!KNonPositiveNat                    \* FiniteSetsExt refuses
\* ASSUME Cases!KZeroStringEqEnum                  \* FiniteSetsExt refuses
\* ASSUME Cases!KZeroPositiveNatEqEnum             \* FiniteSetsExt refuses
\* ASSUME Cases!KSubsetNegativeStringEmpty         \* FiniteSetsExt refuses
\* ASSUME AssertError(
\*   "The second argument of kSubset should be a set, but instead it is:\n42",
\*   Cases!InvalidSecondArgument) \* FiniteSetsExt reports a different error
\* ASSUME Cases!KZeroNatInPowerSet           \* TLC refuses
\* ASSUME Cases!KSubsetNegativeNatInPowerSet \* TLC refuses
\* ASSUME Cases!RcdSetOfKZeroNatFinite       \* TLC refuses
\* ASSUME Cases!RcdSetOfKNegativeNatFinite   \* TLC refuses
\* Comparing different k-subsets of the same infinite base reaches count(),
\* which attempts to evaluate Cardinality(Nat).
\* ASSUME Cases!CardPairKZeroNatKOneNat \* TLC refuses
\* ASSUME Cases!CardPairKOneNatKZeroNat \* TLC refuses

ASSUME Cases!PairInKTwo
ASSUME Cases!SingletonNotInKTwo
ASSUME Cases!EmptyNotInKTwo
ASSUME Cases!EmptyInKZero
\* KSubsetValue#member asks for the candidate's size before noticing that
\* these k-subset families have no elements.
\* ASSUME Cases!ScalarNotInKSubsetNegative \* TLC refuses
\* ASSUME Cases!ScalarNotInKSubsetTooLarge \* TLC refuses

ASSUME Cases!KOneInPowerSet
ASSUME Cases!KTwoInPowerSet
ASSUME Cases!KThreeInPowerSet
ASSUME Cases!KZeroInPowerSet
\* TLC rewrites kSubset(k, A) \subseteq SUBSET B to A \subseteq B.
\* ASSUME Cases!KZeroInEmptyPowerSet             \* TLC answers FALSE
\* ASSUME Cases!KZeroLargerInPowerSet            \* TLC answers FALSE
\* ASSUME Cases!KSubsetTooLargeInSmallerPowerSet \* TLC answers FALSE
\* ASSUME Cases!KSubsetNegativeInSmallerPowerSet \* TLC answers FALSE
ASSUME Cases!PowerSetNotInKOne
ASSUME Cases!PowerSetNotInKTwo
ASSUME Cases!PowerSetNotInKThree
ASSUME Cases!KOneNotInKTwo
ASSUME Cases!KTwoNotInKOne
ASSUME Cases!KOneNotInKThree
ASSUME Cases!KThreeNotInKOne
ASSUME Cases!KTwoNotInKThree
ASSUME Cases!KThreeNotInKTwo
ASSUME Cases!KOneInEnumOne
ASSUME Cases!EnumOneInKOne
ASSUME Cases!KTwoInEnumTwo
ASSUME Cases!EnumTwoInKTwo

ASSUME Cases!KTwoOfFourDiffKTwoOfThree
ASSUME Cases!KTwoOfThreeDiffKTwoOfFour
\* ASSUME Cases!KZeroBaseIndependent \* TLC answers FALSE
ASSUME Cases!KZeroEqEnum
ASSUME Cases!EnumEqKZero
ASSUME Cases!KOneEqEnum
ASSUME Cases!EnumEqKOne
ASSUME Cases!KTwoEqEnum
ASSUME Cases!EnumEqKTwo
ASSUME Cases!KZeroEqSym
ASSUME Cases!KZeroEqSymRev
ASSUME Cases!KOneEqSym
ASSUME Cases!KOneEqSymRev
ASSUME Cases!KTwoEqSym
ASSUME Cases!KTwoEqSymRev
ASSUME Cases!KThreeEqSym
ASSUME Cases!KThreeEqSymRev

\* TLC establishes K \subseteq D and D \subseteq K but violates extensionality
\* by evaluating K = D to FALSE. See issue 1424.
ASSUME Cases!KTwoFourInDefinition
ASSUME Cases!DefinitionInKTwoFour
ASSUME Cases!KTwoFourSymInDefinition
ASSUME Cases!DefinitionInKTwoFourSym
ASSUME Cases!KThreeFourInDefinition
ASSUME Cases!DefinitionInKThreeFour
ASSUME Cases!KThreeFourSymInDefinition
ASSUME Cases!DefinitionInKThreeFourSym
ASSUME Cases!KThreeFiveInDefinition
ASSUME Cases!DefinitionInKThreeFive
ASSUME Cases!KThreeFiveSymInDefinition
ASSUME Cases!DefinitionInKThreeFiveSym

\* KElementEnumerator orders combinations colexicographically (by bit mask);
\* SetEnumValue normalization uses lexicographic Value order. The orders first
\* differ for k=2,n=4 and also differ for k=3,n=5; k=3,n=4 is the adjacent
\* boundary case. SubsetValue#toSetEnum incorrectly marks the colexicographic
\* vector normalized, independently of the representation of the base set.
\* Consequently equality fails and set normalization retains equal elements.
\* ASSUME Cases!KTwoFourEqDefinition       \* TLC answers FALSE
\* ASSUME Cases!DefinitionEqKTwoFour       \* TLC answers FALSE
\* ASSUME Cases!KTwoFourSymEqDefinition    \* TLC answers FALSE
\* ASSUME Cases!DefinitionEqKTwoFourSym    \* TLC answers FALSE
ASSUME Cases!KThreeFourEqDefinition
ASSUME Cases!DefinitionEqKThreeFour
\* The symmetric-base k=3,n=4 boundary has the same order in both
\* representations.
ASSUME Cases!KThreeFourSymEqDefinition
ASSUME Cases!DefinitionEqKThreeFourSym
\* ASSUME Cases!KThreeFiveEqDefinition     \* TLC answers FALSE
\* ASSUME Cases!DefinitionEqKThreeFive     \* TLC answers FALSE
\* ASSUME Cases!KThreeFiveSymEqDefinition \* TLC answers FALSE
\* ASSUME Cases!DefinitionEqKThreeFiveSym \* TLC answers FALSE
\* ASSUME Cases!CardKTwoFourWithDefinition \* TLC answers 2
\* ASSUME Cases!CardDefinitionWithKTwoFour \* TLC answers 2
\* ASSUME Cases!CardKTwoFourSymWithDefinition \* TLC answers 2
\* ASSUME Cases!CardDefinitionWithKTwoFourSym \* TLC answers 2
ASSUME Cases!CardKThreeFourWithDefinition
ASSUME Cases!CardDefinitionWithKThreeFour
ASSUME Cases!CardKThreeFourSymWithDefinition
ASSUME Cases!CardDefinitionWithKThreeFourSym
\* ASSUME Cases!CardKThreeFiveWithDefinition \* TLC answers 2
\* ASSUME Cases!CardDefinitionWithKThreeFive \* TLC answers 2
\* ASSUME Cases!CardKThreeFiveSymWithDefinition \* TLC answers 2
\* ASSUME Cases!CardDefinitionWithKThreeFiveSym \* TLC answers 2

\* ASSUME Cases!KSubsetNormalizedBaseEqDefinition \* TLC refuses for k < 0
\* ASSUME Cases!KSubsetNormalizedBaseBoundsEmpty  \* TLC refuses for k < 0
\* Enumerating the equivalent set-builder expression over 1..27 takes about
\* 30 seconds, while the lazy k-subset finishes in under a second.
ASSUME Cases!KSubsetFullLargeBase
ASSUME Cases!EmptyNotInKOneThree
ASSUME Cases!KSubsetMembershipAgreesWithDefinition

\* Evaluating [n1 : S] requires deciding whether S is empty and thus reaches
\* Value#isEmpty with S represented by a KSubsetValue.
ASSUME Cases!RcdSetOfKSubsetReflexive

\* ASSUME Cases!KOneDiffKTwo \* TLC answers FALSE
\* ASSUME Cases!KTwoDiffKOne \* TLC answers FALSE
\* ASSUME Cases!KOneDiffKThree \* TLC answers FALSE
\* ASSUME Cases!KThreeDiffKOne \* TLC answers FALSE
\* ASSUME Cases!KTwoDiffKThree \* TLC answers FALSE
\* ASSUME Cases!KThreeDiffKTwo \* TLC answers FALSE
\* ASSUME Cases!KOneDiffPowerSet \* TLC answers FALSE
\* ASSUME Cases!KTwoDiffPowerSet \* TLC answers FALSE
\* ASSUME Cases!KThreeDiffPowerSet \* TLC answers FALSE
\* ASSUME Cases!PowerSetDiffKOne \* TLC answers FALSE
\* ASSUME Cases!PowerSetDiffKTwo \* TLC answers FALSE
\* ASSUME Cases!PowerSetDiffKThree \* TLC answers FALSE
\* ASSUME Cases!KOneSingletonDiff \* TLC answers FALSE
\* ASSUME Cases!KOneSingletonDiffRev \* TLC answers FALSE
\* ASSUME Cases!KTwoNotInPowerSetSingleton \* TLC answers FALSE

\* Both source orders exercise the two receiver directions of Value#compareTo.
ASSUME Cases!CardPairKOneKTwo
ASSUME Cases!CardPairKTwoKOne
ASSUME Cases!CardPairKOneKThree
ASSUME Cases!CardPairKThreeKOne
ASSUME Cases!CardPairKTwoKThree
ASSUME Cases!CardPairKThreeKTwo
ASSUME Cases!CardPairKTwoEightKOneFive
ASSUME Cases!CardPairKOneFiveKTwoEight
ASSUME Cases!CardPairKThreeSixKOneTwenty
ASSUME Cases!CardPairKOneTwentyKThreeSix
ASSUME Cases!CardTripleKs
ASSUME Cases!CardTripleKsRev
ASSUME Cases!CardPairPowerSetKTwo
\* ASSUME Cases!CardPairKTwoPowerSet \* TLC answers 1
\* ASSUME Cases!CardTripleKsPowerSet \* TLC answers 2
ASSUME Cases!CardTriplePowerSetKs

\* Set normalization sorts by Value#compareTo and removes adjacent equal
\* values. Hence a k-subset and its explicit enumeration must occupy one
\* equivalence class in every enclosing set.
ASSUME Cases!CardKZeroWithEnum
ASSUME Cases!CardEnumWithKZero
ASSUME Cases!CardKOneWithEnum
ASSUME Cases!CardEnumWithKOne
ASSUME Cases!CardKTwoWithEnum
ASSUME Cases!CardEnumWithKTwo
ASSUME Cases!CardKZeroWithSym
ASSUME Cases!CardKZeroWithSymRev
ASSUME Cases!CardKOneWithSym
ASSUME Cases!CardKOneWithSymRev
ASSUME Cases!CardKTwoWithSym
ASSUME Cases!CardKTwoWithSymRev
ASSUME Cases!CardKThreeWithSym
ASSUME Cases!CardKThreeWithSymRev
ASSUME Cases!CardKSubsetTooLargeWithEmpty
ASSUME Cases!CardEmptyWithKSubsetTooLarge
ASSUME Cases!CardKSubsetNegativeWithEmpty
ASSUME Cases!CardEmptyWithKSubsetNegative
ASSUME Cases!CardKsWithEnumOne
\* ASSUME Cases!CardKsWithEnumOneRev \* TLC answers 3
ASSUME Cases!CardKsWithEnumTwo
ASSUME Cases!CardKsWithEnumTwoRev
ASSUME Cases!CardEnumsWithKs
\* ASSUME Cases!CardKsWithEnums \* TLC answers 4
\* ASSUME Cases!CardTripleKsWithEnums \* TLC answers 5
ASSUME Cases!CardTripleKsWithEnumsRev

\* TLCFP deep-normalizes its argument. Extensionally equal k-subsets and
\* explicit sets must therefore have equal fingerprints, including inside
\* mixed sets whose equal elements normalization must coalesce.
ASSUME Cases!FPKOneEqEnum
ASSUME Cases!FPKTwoEqEnum
ASSUME Cases!FPKZeroEqSym
ASSUME Cases!FPKOneEqSym
ASSUME Cases!FPKTwoEqSym
ASSUME Cases!FPKThreeEqSym
ASSUME Cases!FPKOneDiffKTwo
ASSUME Cases!FPKSubsetTooLargeEqEmpty
ASSUME Cases!FPKSubsetNegativeEqEmpty
\* ASSUME Cases!FPKTwoFourEqDefinition \* TLC answers FALSE
\* ASSUME Cases!FPKTwoFourSymEqDefinition \* TLC answers FALSE
ASSUME Cases!FPKThreeFourEqDefinition
ASSUME Cases!FPKThreeFourSymEqDefinition
\* ASSUME Cases!FPKThreeFiveEqDefinition \* TLC answers FALSE
\* ASSUME Cases!FPKThreeFiveSymEqDefinition \* TLC answers FALSE
\* ASSUME Cases!FPPairKTwoEightKOneFiveOrderIndependent \* TLC answers FALSE
\* Equal binomial counts, different k values, and different bases fall
\* through KSubsetValue#compareTo into the SubsetValue comparison in both
\* directions, making the enclosing set's normalized order source-dependent.
\* ASSUME Cases!FPPairKThreeSixKOneTwentyOrderIndependent \* TLC returns FALSE
\* ASSUME Cases!FPMixedEqEnums \* TLC answers FALSE
ASSUME Cases!FPMixedEqEnumsRev
\* ASSUME Cases!FPMixedOrderIndependent \* TLC answers FALSE

\* Cardinality(kSubset(k, S)) is "Cardinality(S) choose k" and requires no
\* enumeration of kSubset(k, S).
ASSUME Cases!KSubsetLargeFinite
ASSUME Cases!PairInKSubsetLarge
\* ASSUME Cases!CardKSubsetLarge \* TLC refuses (k=2 and n=64)
\* ASSUME Cases!CardKSubsetAllLarge \* TLC refuses (k=64 and n=64)
\* ASSUME Cases!CardKSubsetAllButOneLarge \* TLC refuses (k=63 and n=64)
ASSUME Cases!CardKSubsetAllMaxEnumerable
\* These cases require "n choose k" = "n choose (n-k)"; computing through the
\* middle of Pascal's triangle is infeasible.
\* ASSUME Cases!CardKSubsetAllMillion \* TLC refuses (k=1000000 and n=1000000)
\* ASSUME Cases!CardKSubsetAllButOneMillion \* TLC refuses (k=999999 and n=1000000)
\* Both source orders compare the two lazy values without enumerating either.
ASSUME Cases!CardPairK31K32Large
ASSUME Cases!CardPairK32K31Large
\* Different bases and k values remain distinct without enumerating either.
ASSUME Cases!CardPairK31LargeK2Small
ASSUME Cases!CardPairK2SmallK31Large

\* "64 choose 32" exceeds Integer.MAX_VALUE. Because Value#size returns int,
\* TLC cannot evaluate even reflexive equality of this cardinality.
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value),\nbut it produced the following error:\nk=32 and n=64",
                   Cases!CardKSubsetMiddleLargeReflexive)

\* Extensional comparison of SUBSET (1..64) with a k-subset would enumerate
\* 2^64 elements. Before the comparison fix TLC returns FALSE for both
\* disequalities; afterward it rejects both evaluations.
\* ASSUME Cases!KSubsetLargeDiffPowerSet \* TLC answers FALSE or refuses
\* ASSUME Cases!PowerSetLargeDiffKSubset \* TLC answers FALSE or refuses
\* Normalization reaches Value#compareTo in both source orders.
\* ASSUME Cases!CardPairKSubsetPowerSetLarge \* TLC refuses
\* ASSUME Cases!CardPairPowerSetKSubsetLarge \* TLC refuses

ASSUME ToString(Cases!K2) = "{{1, 2}, {1, 3}, {2, 3}}"
\* ASSUME ToString(Cases!K24) = \* TLC answers in colex order ({2, 3} before {1, 4})
\*     "{{1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}}"
\* ASSUME ToString(Cases!K24Sym) = \* TLC answers in colex order ({2, 3} before {1, 4})
\*     "{{1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}}"
ASSUME ToString(Cases!K34) =
    "{{1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}}"
\* ASSUME ToString(Cases!K35) = \* TLC answers in colex order ({1, 3, 4} before {1, 2, 5})
\*     "{{1, 2, 3}, {1, 2, 4}, {1, 2, 5}, {1, 3, 4}, {1, 3, 5}, {1, 4, 5}, {2, 3, 4}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}}"
\* ASSUME ToString(kSubset(2, 1..8)) = \* TLC answers in colex order ({2, 3} before {1, 4})
\*     "{{1, 2}, {1, 3}, {1, 4}, {1, 5}, {1, 6}, {1, 7}, {1, 8}, {2, 3}, {2, 4}, {2, 5}, {2, 6}, {2, 7}, {2, 8}, {3, 4}, {3, 5}, {3, 6}, {3, 7}, {3, 8}, {4, 5}, {4, 6}, {4, 7}, {4, 8}, {5, 6}, {5, 7}, {5, 8}, {6, 7}, {6, 8}, {7, 8}}"
\* ASSUME ToString(kSubset(63, 1..63)) = \* TLC answers with the defining set expression
\*     "{{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63}}"

\* Above the expansion threshold, ToString emits the defining set expression.
\* ASSUME ToString(kSubset(2, 1..12)) = \* TLC answers "SUBSET (1..12)"
\*     "{s \\in SUBSET ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}) : Cardinality(s) = 2}"

-----------------------------------------------------------------------------
\* Cardinality and enumerability are independent. A cardinality greater than
\* Integer.MAX_VALUE is unrepresentable, while a small cardinality does not
\* make the base set enumerable by KElementEnumerator's 63-bit representation.
\* Thus "64 choose 64" = 1, but expansion is still rejected.

\* ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLC.ToString(tlc2.value.impl.Value),\nbut it produced the following error:\nk=32 and n=64", \* TLC answers "SUBSET (1..64)" instead of error
\*                    ToString(kSubset(32, 1..64)) = "")
\* ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLC.ToString(tlc2.value.impl.Value),\nbut it produced the following error:\nk=64 and n=64", \* TLC answers "SUBSET (1..64)" instead of error
\*                    ToString(kSubset(64, 1..64)) = "")
=============================================================================
