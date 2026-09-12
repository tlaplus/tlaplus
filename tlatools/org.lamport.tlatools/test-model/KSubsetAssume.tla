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
ASSUME Cases!KZeroNestedEnumeration

ASSUME Cases!CardKZeroNat
ASSUME Cases!CardKSubsetNegativeNat
ASSUME Cases!KZeroNatFinite
ASSUME Cases!KSubsetNegativeNatFinite
ASSUME Cases!KOneNatInfinite
\* These memberships do not require enumerating the infinite base.
ASSUME Cases!EmptyInKZeroNat
ASSUME Cases!EmptyNotInKSubsetNegativeNat
ASSUME Cases!SingletonNotInKZeroNat
ASSUME Cases!SingletonInKOneNat
ASSUME Cases!EmptyInKZeroString
ASSUME Cases!EmptyNotInKSubsetNegativeString
\* Pin TLC's representation-independent answers for non-finite bases.
ASSUME Cases!KZeroNatEqEnum
ASSUME Cases!KSubsetNegativeNatEmpty
ASSUME Cases!KNonPositiveNat
ASSUME Cases!KZeroStringEqEnum
ASSUME Cases!KZeroPositiveNatEqEnum
ASSUME Cases!KSubsetNegativeStringEmpty
ASSUME AssertError(
  "The second argument of kSubset should be a set, but instead it is:\n42",
  Cases!InvalidSecondArgument)
\* Nat is not enumerable, so the power-set rewrite does not apply and
\* TLC enumerates the trivial k-subset.
ASSUME Cases!KZeroNatInPowerSet
ASSUME Cases!KSubsetNegativeNatInPowerSet
ASSUME Cases!RcdSetOfKZeroNatFinite
ASSUME Cases!RcdSetOfKNegativeNatFinite
\* Different k values order k-subsets of the same infinite base without
\* asking for the base's cardinality.
ASSUME Cases!CardPairKZeroNatKOneNat
ASSUME Cases!CardPairKOneNatKZeroNat

ASSUME Cases!PairInKTwo
ASSUME Cases!SingletonNotInKTwo
ASSUME Cases!EmptyNotInKTwo
ASSUME Cases!EmptyInKZero
ASSUME Cases!ScalarNotInKSubsetNegative
ASSUME Cases!ScalarNotInKSubsetTooLarge

ASSUME Cases!KOneInPowerSet
ASSUME Cases!KTwoInPowerSet
ASSUME Cases!KThreeInPowerSet
ASSUME Cases!KZeroInPowerSet
ASSUME Cases!KZeroInEmptyPowerSet
ASSUME Cases!KZeroLargerInPowerSet
ASSUME Cases!KSubsetTooLargeInSmallerPowerSet
ASSUME Cases!KSubsetNegativeInSmallerPowerSet
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
ASSUME Cases!KZeroBaseIndependent
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

\* These inclusion checks and the equality and fingerprint checks below ensure
\* that kSubset agrees extensionally with its definition. See issue 1424.
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

\* These exercise the first sizes at which lexicographic and
\* colexicographic combination order differ.
ASSUME Cases!KTwoFourEqDefinition
ASSUME Cases!DefinitionEqKTwoFour
ASSUME Cases!KTwoFourSymEqDefinition
ASSUME Cases!DefinitionEqKTwoFourSym
ASSUME Cases!KThreeFourEqDefinition
ASSUME Cases!DefinitionEqKThreeFour
ASSUME Cases!KThreeFourSymEqDefinition
ASSUME Cases!DefinitionEqKThreeFourSym
ASSUME Cases!KThreeFiveEqDefinition
ASSUME Cases!DefinitionEqKThreeFive
ASSUME Cases!KThreeFiveSymEqDefinition
ASSUME Cases!DefinitionEqKThreeFiveSym
ASSUME Cases!CardKTwoFourWithDefinition
ASSUME Cases!CardDefinitionWithKTwoFour
ASSUME Cases!CardKTwoFourSymWithDefinition
ASSUME Cases!CardDefinitionWithKTwoFourSym
ASSUME Cases!CardKThreeFourWithDefinition
ASSUME Cases!CardDefinitionWithKThreeFour
ASSUME Cases!CardKThreeFourSymWithDefinition
ASSUME Cases!CardDefinitionWithKThreeFourSym
ASSUME Cases!CardKThreeFiveWithDefinition
ASSUME Cases!CardDefinitionWithKThreeFive
ASSUME Cases!CardKThreeFiveSymWithDefinition
ASSUME Cases!CardDefinitionWithKThreeFiveSym

ASSUME Cases!KSubsetNormalizedBaseEqDefinition
ASSUME Cases!KSubsetNormalizedBaseBoundsEmpty
\* Enumerating the equivalent set-builder expression over 1..27 takes about
\* 30 seconds, while the lazy k-subset finishes in under a second.
ASSUME Cases!KSubsetFullLargeBase
ASSUME Cases!EmptyNotInKOneThree
ASSUME Cases!KSubsetMembershipAgreesWithDefinition

\* Evaluating [n1 : S] requires deciding whether S is empty and thus reaches
\* Value#isEmpty with S represented by a KSubsetValue.
ASSUME Cases!RcdSetOfKSubsetReflexive

ASSUME Cases!KOneDiffKTwo
ASSUME Cases!KTwoDiffKOne
ASSUME Cases!KOneDiffKThree
ASSUME Cases!KThreeDiffKOne
ASSUME Cases!KTwoDiffKThree
ASSUME Cases!KThreeDiffKTwo
ASSUME Cases!KOneDiffPowerSet
ASSUME Cases!KTwoDiffPowerSet
ASSUME Cases!KThreeDiffPowerSet
ASSUME Cases!PowerSetDiffKOne
ASSUME Cases!PowerSetDiffKTwo
ASSUME Cases!PowerSetDiffKThree
ASSUME Cases!KOneSingletonDiff
ASSUME Cases!KOneSingletonDiffRev
ASSUME Cases!KTwoNotInPowerSetSingleton

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
ASSUME Cases!CardPairKTwoPowerSet
ASSUME Cases!CardTripleKsPowerSet
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
ASSUME Cases!CardKsWithEnumOneRev
ASSUME Cases!CardKsWithEnumTwo
ASSUME Cases!CardKsWithEnumTwoRev
ASSUME Cases!CardEnumsWithKs
ASSUME Cases!CardKsWithEnums
ASSUME Cases!CardTripleKsWithEnums
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
ASSUME Cases!FPKTwoFourEqDefinition
ASSUME Cases!FPKTwoFourSymEqDefinition
ASSUME Cases!FPKThreeFourEqDefinition
ASSUME Cases!FPKThreeFourSymEqDefinition
ASSUME Cases!FPKThreeFiveEqDefinition
ASSUME Cases!FPKThreeFiveSymEqDefinition
ASSUME Cases!FPPairKTwoEightKOneFiveOrderIndependent
\* Equal binomial counts, different k values, and different bases fall
\* through the KSubsetValue comparison without being treated as power sets.
ASSUME Cases!FPPairKThreeSixKOneTwentyOrderIndependent
ASSUME Cases!FPMixedEqEnums
ASSUME Cases!FPMixedEqEnumsRev
ASSUME Cases!FPMixedOrderIndependent

\* Cardinality(kSubset(k, S)) is "Cardinality(S) choose k" and requires no
\* enumeration of kSubset(k, S).
ASSUME Cases!KSubsetLargeFinite
ASSUME Cases!PairInKSubsetLarge
ASSUME Cases!CardKSubsetLarge
ASSUME Cases!CardKSubsetAllLarge
ASSUME Cases!CardKSubsetAllButOneLarge
ASSUME Cases!CardKSubsetAllMaxEnumerable
\* These cases require "n choose k" = "n choose (n-k)"; computing through the
\* middle of Pascal's triangle is infeasible.
ASSUME Cases!CardKSubsetAllMillion
ASSUME Cases!CardKSubsetAllButOneMillion
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

\* Extensional comparison must not enumerate either of these sets.
ASSUME Cases!KSubsetLargeDiffPowerSet
ASSUME Cases!PowerSetLargeDiffKSubset
\* Both orders reach Value#compareTo while normalizing the enclosing set.
ASSUME Cases!CardPairKSubsetPowerSetLarge
ASSUME Cases!CardPairPowerSetKSubsetLarge

ASSUME ToString(Cases!K2) = "{{1, 2}, {1, 3}, {2, 3}}"
ASSUME ToString(Cases!K24) =
    "{{1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}}"
ASSUME ToString(Cases!K24Sym) =
    "{{1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}}"
ASSUME ToString(Cases!K34) =
    "{{1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}}"
ASSUME ToString(Cases!K35) =
    "{{1, 2, 3}, {1, 2, 4}, {1, 2, 5}, {1, 3, 4}, {1, 3, 5}, {1, 4, 5}, {2, 3, 4}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}}"
ASSUME ToString(kSubset(2, 1..8)) =
    "{{1, 2}, {1, 3}, {1, 4}, {1, 5}, {1, 6}, {1, 7}, {1, 8}, {2, 3}, {2, 4}, {2, 5}, {2, 6}, {2, 7}, {2, 8}, {3, 4}, {3, 5}, {3, 6}, {3, 7}, {3, 8}, {4, 5}, {4, 6}, {4, 7}, {4, 8}, {5, 6}, {5, 7}, {5, 8}, {6, 7}, {6, 8}, {7, 8}}"
ASSUME ToString(kSubset(63, 1..63)) =
    "{{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63}}"

\* Above the expansion threshold, ToString emits the defining set expression.
ASSUME ToString(kSubset(2, 1..12)) =
    "{s \\in SUBSET (1..12) : Cardinality(s) = 2}"

-----------------------------------------------------------------------------
\* A cardinality greater than Integer.MAX_VALUE is unrepresentable.

ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLC.ToString(tlc2.value.impl.Value),\nbut it produced the following error:\nk=32 and n=64",
                   ToString(kSubset(32, 1..64)) = "")
ASSUME ToString(kSubset(64, 1..64)) =
    "{{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64}}"
=============================================================================
