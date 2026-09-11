------------------------------- MODULE KSubsetCases -------------------------
\* Propositions about the set of all k-element subsets of a set.
\* KSubsetAssume asserts them for TLC's interpretation of
\* FiniteSetsExt!kSubset. KSubsetTheorems proves the finite-base propositions
\* from its set-builder definition; the infinite-base propositions below
\* specify TLC behavior because Cardinality is unspecified for infinite sets.
\*
\* The operators are parameters so each INSTANCE can substitute the
\* interpretation available to its tool. TLAPS does not read
\* CommunityModules.jar or know theorems about FiniteSetsExt's local
\* Cardinality. TLC interprets TLCFP as a fingerprint; the proof instance
\* substitutes the identity operator. Keeping ASSUME declarations out of this
\* module prevents them from becoming hypotheses of its theorems.
\*
\* See https://github.com/tlaplus/tlaplus/issues/1415 and
\* https://github.com/tlaplus/tlaplus/issues/1424
EXTENDS Integers

CONSTANTS kSubset(_, _), Cardinality(_), IsFiniteSet(_), TLCFP(_)

K0     == kSubset(0, 1..3)   \* {{}}
K1     == kSubset(1, 1..3)   \* {{1}, {2}, {3}}
K2     == kSubset(2, 1..3)   \* {{1, 2}, {1, 3}, {2, 3}}
K3     == kSubset(3, 1..3)   \* {{1, 2, 3}}
K0Sym  == kSubset(0, {1, 2, 3})
K1Sym  == kSubset(1, {1, 2, 3})
K2Sym  == kSubset(2, {1, 2, 3})
K3Sym  == kSubset(3, {1, 2, 3})
P      == SUBSET (1..3)      \* eight elements
E0     == {{}}
E1     == {{1}, {2}, {3}}    \* K1 written out
E2     == {{1, 2}, {1, 3}, {2, 3}}
K24    == kSubset(2, 1..4)
D24    == {s \in SUBSET (1..4) : Cardinality(s) = 2}
K24Sym == kSubset(2, {1, 2, 3, 4})
K34    == kSubset(3, 1..4)
D34    == {s \in SUBSET (1..4) : Cardinality(s) = 3}
K34Sym == kSubset(3, {1, 2, 3, 4})
K35    == kSubset(3, 1..5)
D35    == {s \in SUBSET (1..5) : Cardinality(s) = 3}
K35Sym == kSubset(3, {1, 2, 3, 4, 5})
K28    == kSubset(2, 1..8)
K15    == kSubset(1, 1..5)
K36    == kSubset(3, 1..6)
K120   == kSubset(1, 1..20)

-----------------------------------------------------------------------------
\* How many k-subsets a base set has, and how large each of them is.

CardKZero                 == Cardinality(K0) = 1
CardKOne                  == Cardinality(K1) = 3
CardKTwo                  == Cardinality(K2) = 3
CardKThree                == Cardinality(K3) = 1
KTwoElementCardinality    == \A s \in K2 : Cardinality(s) = 2
KSubsetTooLargeEmpty      == kSubset(4, 1..3) = {}
KSubsetNegativeEmpty      == kSubset(-1, 1..3) = {}
CardKSubsetTooLarge       == Cardinality(kSubset(4, 1..3)) = 0
CardKSubsetNegative       == Cardinality(kSubset(-1, 1..3)) = 0
EmptyBaseKZeroUnit        == kSubset(0, {}) = {{}}
EmptyBaseKOneEmpty        == kSubset(1, {}) = {}
EmptyEqKSubsetTooLarge    == {} = kSubset(4, 1..3)
EmptyEqKSubsetNegative    == {} = kSubset(-1, 1..3)
KZeroNestedEnumeration    ==
  \A K \in {K0} : \A x \in K : \A y \in K : x = y

-----------------------------------------------------------------------------
\* Trivial k-subsets of a base whose cardinality TLC cannot evaluate.

CardKZeroNat              == Cardinality(kSubset(0, Nat)) = 1
CardKSubsetNegativeNat    == Cardinality(kSubset(-1, Nat)) = 0
KZeroNatFinite            == IsFiniteSet(kSubset(0, Nat))
KSubsetNegativeNatFinite  == IsFiniteSet(kSubset(-1, Nat))
KOneNatInfinite           == ~IsFiniteSet(kSubset(1, Nat))
EmptyInKZeroNat           == {} \in kSubset(0, Nat)
EmptyNotInKSubsetNegativeNat == {} \notin kSubset(-1, Nat)
SingletonNotInKZeroNat    == {1} \notin kSubset(0, Nat)
SingletonInKOneNat        == {1} \in kSubset(1, Nat)
EmptyInKZeroString        == {} \in kSubset(0, STRING)
EmptyNotInKSubsetNegativeString == {} \notin kSubset(-1, STRING)
KZeroNatEqEnum            == kSubset(0, Nat) = {{}}
KSubsetNegativeNatEmpty   == kSubset(-1, Nat) = {}
KNonPositiveNat           == \A k \in -3..0 : kSubset(k, Nat) = IF k = 0 THEN {{}} ELSE {}
KZeroStringEqEnum         == kSubset(0, STRING) = {{}}
KZeroPositiveNatEqEnum    == kSubset(0, Nat \ {0}) = {{}}
KSubsetNegativeStringEmpty == kSubset(-1, STRING) = {}
KZeroNatInPowerSet           == kSubset(0, Nat) \subseteq P
KSubsetNegativeNatInPowerSet == kSubset(-1, Nat) \subseteq P
RcdSetOfKZeroNatFinite    == IsFiniteSet([n1 : kSubset(0, Nat)])
RcdSetOfKNegativeNatFinite == IsFiniteSet([n1 : kSubset(-1, Nat)])
CardPairKZeroNatKOneNat   == Cardinality({kSubset(0, Nat), kSubset(1, Nat)}) = 2
CardPairKOneNatKZeroNat   == Cardinality({kSubset(1, Nat), kSubset(0, Nat)}) = 2
InvalidSecondArgument     == kSubset(0, 42)

-----------------------------------------------------------------------------
\* What a k-subset holds, and where it sits in the power set of its base set.

PairInKTwo         == {1, 2} \in K2
SingletonNotInKTwo == {1} \notin K2
EmptyNotInKTwo     == {} \notin K2
EmptyInKZero       == {} \in K0
ScalarNotInKSubsetNegative == 1 \notin kSubset(-1, 1..3)
ScalarNotInKSubsetTooLarge == 1 \notin kSubset(4, 1..3)

KOneInPowerSet      == K1 \subseteq P
KTwoInPowerSet      == K2 \subseteq P
KThreeInPowerSet    == K3 \subseteq P
\* SUBSET S always contains {}. The rewrite of
\* (kSubset(k, A) \subseteq SUBSET B) to (A \subseteq B) is therefore
\* wrong when the k-subset is {{}} or {}.
KZeroInPowerSet                  == K0 \subseteq P
KZeroInEmptyPowerSet             == K0 \subseteq SUBSET {}
KZeroLargerInPowerSet            == kSubset(0, 1..4) \subseteq P
KSubsetTooLargeInSmallerPowerSet == kSubset(4, 1..3) \subseteq SUBSET (1..2)
KSubsetNegativeInSmallerPowerSet == kSubset(-1, 1..3) \subseteq SUBSET (1..2)
PowerSetNotInKOne   == ~(P \subseteq K1)
PowerSetNotInKTwo   == ~(P \subseteq K2)
PowerSetNotInKThree == ~(P \subseteq K3)
KOneNotInKTwo       == ~(K1 \subseteq K2)
KTwoNotInKOne       == ~(K2 \subseteq K1)
KOneNotInKThree     == ~(K1 \subseteq K3)
KThreeNotInKOne     == ~(K3 \subseteq K1)
KTwoNotInKThree     == ~(K2 \subseteq K3)
KThreeNotInKTwo     == ~(K3 \subseteq K2)
KOneInEnumOne       == K1 \subseteq E1
EnumOneInKOne       == E1 \subseteq K1
KTwoInEnumTwo       == K2 \subseteq E2
EnumTwoInKTwo       == E2 \subseteq K2

-----------------------------------------------------------------------------
\* A k-subset against a k-subset of another base set, and against the set it
\* is written out as, in both orders.

KTwoOfFourDiffKTwoOfThree == kSubset(2, 1..4) # K2
KTwoOfThreeDiffKTwoOfFour == K2 # kSubset(2, 1..4)
KZeroBaseIndependent      == K0 = kSubset(0, 1..4)
KZeroEqEnum                == K0 = E0
EnumEqKZero                == E0 = K0
KOneEqEnum                 == K1 = E1
EnumEqKOne                 == E1 = K1
KTwoEqEnum                 == K2 = E2
EnumEqKTwo                 == E2 = K2
KZeroEqSym                 == K0Sym = K0
KZeroEqSymRev              == K0 = K0Sym
KOneEqSym                  == K1Sym = K1
KOneEqSymRev               == K1 = K1Sym
KTwoEqSym                  == K2Sym = K2
KTwoEqSymRev               == K2 = K2Sym
KThreeEqSym                == K3Sym = K3
KThreeEqSymRev             == K3 = K3Sym
KTwoFourInDefinition       == K24 \subseteq D24
DefinitionInKTwoFour       == D24 \subseteq K24
KTwoFourSymInDefinition    == K24Sym \subseteq D24
DefinitionInKTwoFourSym    == D24 \subseteq K24Sym
KThreeFourInDefinition     == K34 \subseteq D34
DefinitionInKThreeFour     == D34 \subseteq K34
KThreeFourSymInDefinition  == K34Sym \subseteq D34
DefinitionInKThreeFourSym  == D34 \subseteq K34Sym
KThreeFiveInDefinition     == K35 \subseteq D35
DefinitionInKThreeFive     == D35 \subseteq K35
KThreeFiveSymInDefinition  == K35Sym \subseteq D35
DefinitionInKThreeFiveSym  == D35 \subseteq K35Sym
KTwoFourEqDefinition       == K24 = D24
DefinitionEqKTwoFour       == D24 = K24
KTwoFourSymEqDefinition    == K24Sym = D24
DefinitionEqKTwoFourSym    == D24 = K24Sym
KThreeFourEqDefinition     == K34 = D34
DefinitionEqKThreeFour     == D34 = K34
KThreeFourSymEqDefinition  == K34Sym = D34
DefinitionEqKThreeFourSym  == D34 = K34Sym
KThreeFiveEqDefinition     == K35 = D35
DefinitionEqKThreeFive     == D35 = K35
KThreeFiveSymEqDefinition  == K35Sym = D35
DefinitionEqKThreeFiveSym  == D35 = K35Sym

KSubsetNormalizedBaseEqDefinition ==
  LET S == {"a", "b", "c", "c"}
  IN \A k \in -1..Cardinality(S) + 1 :
       kSubset(k, S) = {s \in SUBSET S : Cardinality(s) = k}

KSubsetNormalizedBaseBoundsEmpty ==
  LET S == {"a", "b", "c", "c"}
  IN kSubset(-1, S) = {} /\ kSubset(4, S) = {}

KSubsetFullLargeBase ==
  LET S == 1..27
  IN kSubset(Cardinality(S), S) = {S}

EmptyNotInKOneThree == {} \notin kSubset(1, {1, 2, 3})

KSubsetMembershipAgreesWithDefinition ==
  LET T == 1..3
  IN \A k \in 1..Cardinality(T) :
       /\ \A e \in {s \in SUBSET T : Cardinality(s) = k} :
            e \in kSubset(k, T)
       /\ \A e \in {s \in SUBSET T : Cardinality(s) # k} :
            e \notin kSubset(k, T)

RcdSetOfKSubsetReflexive == [n1 : kSubset(32, 1..64)] = [n1 : kSubset(32, 1..64)]

-----------------------------------------------------------------------------
\* Two k-subsets of one base set, and a k-subset against the power set of it.

KOneDiffKTwo   == K1 # K2
KTwoDiffKOne   == K2 # K1
KOneDiffKThree == K1 # K3
KThreeDiffKOne == K3 # K1
KTwoDiffKThree == K2 # K3
KThreeDiffKTwo == K3 # K2

KOneDiffPowerSet   == K1 # P
KTwoDiffPowerSet   == K2 # P
KThreeDiffPowerSet == K3 # P
PowerSetDiffKOne   == P # K1
PowerSetDiffKTwo   == P # K2
PowerSetDiffKThree == P # K3

KOneSingletonDiff          == {K1} # {K2}
KOneSingletonDiffRev       == {K2} # {K1}
KTwoNotInPowerSetSingleton == K2 \notin {P}

-----------------------------------------------------------------------------
\* How many elements a set that holds k-subsets has, which rests on which of
\* them it holds apart.

CardPairKOneKTwo           == Cardinality({K1, K2}) = 2
CardPairKTwoKOne           == Cardinality({K2, K1}) = 2
CardPairKOneKThree         == Cardinality({K1, K3}) = 2
CardPairKThreeKOne         == Cardinality({K3, K1}) = 2
CardPairKTwoKThree         == Cardinality({K2, K3}) = 2
CardPairKThreeKTwo         == Cardinality({K3, K2}) = 2
CardPairKTwoEightKOneFive == Cardinality({K28, K15}) = 2
CardPairKOneFiveKTwoEight == Cardinality({K15, K28}) = 2
CardPairKThreeSixKOneTwenty == Cardinality({K36, K120}) = 2
CardPairKOneTwentyKThreeSix == Cardinality({K120, K36}) = 2
CardTripleKs               == Cardinality({K1, K2, K3}) = 3
CardTripleKsRev            == Cardinality({K3, K2, K1}) = 3

CardPairPowerSetKTwo       == Cardinality({P, K2}) = 2
CardPairKTwoPowerSet       == Cardinality({K2, P}) = 2
CardTripleKsPowerSet       == Cardinality({K1, K2, P}) = 3
CardTriplePowerSetKs       == Cardinality({P, K2, K1}) = 3

CardKZeroWithEnum          == Cardinality({K0, E0}) = 1
CardEnumWithKZero          == Cardinality({E0, K0}) = 1
CardKOneWithEnum           == Cardinality({K1, E1}) = 1
CardEnumWithKOne           == Cardinality({E1, K1}) = 1
CardKTwoWithEnum           == Cardinality({K2, E2}) = 1
CardEnumWithKTwo           == Cardinality({E2, K2}) = 1
CardKZeroWithSym           == Cardinality({K0, K0Sym}) = 1
CardKZeroWithSymRev        == Cardinality({K0Sym, K0}) = 1
CardKOneWithSym            == Cardinality({K1, K1Sym}) = 1
CardKOneWithSymRev         == Cardinality({K1Sym, K1}) = 1
CardKTwoWithSym            == Cardinality({K2, K2Sym}) = 1
CardKTwoWithSymRev         == Cardinality({K2Sym, K2}) = 1
CardKThreeWithSym          == Cardinality({K3, K3Sym}) = 1
CardKThreeWithSymRev       == Cardinality({K3Sym, K3}) = 1
CardKTwoFourWithDefinition == Cardinality({K24, D24}) = 1
CardDefinitionWithKTwoFour == Cardinality({D24, K24}) = 1
CardKTwoFourSymWithDefinition  == Cardinality({K24Sym, D24}) = 1
CardDefinitionWithKTwoFourSym  == Cardinality({D24, K24Sym}) = 1
CardKThreeFourWithDefinition   == Cardinality({K34, D34}) = 1
CardDefinitionWithKThreeFour   == Cardinality({D34, K34}) = 1
CardKThreeFourSymWithDefinition == Cardinality({K34Sym, D34}) = 1
CardDefinitionWithKThreeFourSym == Cardinality({D34, K34Sym}) = 1
CardKThreeFiveWithDefinition   == Cardinality({K35, D35}) = 1
CardDefinitionWithKThreeFive   == Cardinality({D35, K35}) = 1
CardKThreeFiveSymWithDefinition == Cardinality({K35Sym, D35}) = 1
CardDefinitionWithKThreeFiveSym == Cardinality({D35, K35Sym}) = 1

CardKSubsetTooLargeWithEmpty == Cardinality({kSubset(4, 1..3), {}}) = 1
CardEmptyWithKSubsetTooLarge == Cardinality({{}, kSubset(4, 1..3)}) = 1
CardKSubsetNegativeWithEmpty == Cardinality({kSubset(-1, 1..3), {}}) = 1
CardEmptyWithKSubsetNegative == Cardinality({{}, kSubset(-1, 1..3)}) = 1

CardKsWithEnumOne         == Cardinality({K1, K2, E1}) = 2
CardKsWithEnumOneRev      == Cardinality({E1, K2, K1}) = 2
CardKsWithEnumTwo         == Cardinality({K1, E2, K2}) = 2
CardKsWithEnumTwoRev      == Cardinality({K2, E2, K1}) = 2
CardEnumsWithKs           == Cardinality({E2, E1, K2, K1}) = 2
CardKsWithEnums           == Cardinality({K1, K2, E1, E2}) = 2

CardTripleKsWithEnums    == Cardinality({K1, K2, K3, E1, E2}) = 3
CardTripleKsWithEnumsRev == Cardinality({E2, E1, K3, K2, K1}) = 3

-----------------------------------------------------------------------------
\* Fingerprinting deep-normalizes its argument. Equal values must therefore
\* have equal fingerprints regardless of representation or element order.

FPKOneEqEnum               == TLCFP(K1) = TLCFP(E1)
FPKTwoEqEnum               == TLCFP(K2) = TLCFP(E2)
FPKZeroEqSym               == TLCFP(K0) = TLCFP(K0Sym)
FPKOneEqSym                == TLCFP(K1) = TLCFP(K1Sym)
FPKTwoEqSym                == TLCFP(K2) = TLCFP(K2Sym)
FPKThreeEqSym              == TLCFP(K3) = TLCFP(K3Sym)
FPKOneDiffKTwo             == TLCFP(K1) # TLCFP(K2)
FPKSubsetTooLargeEqEmpty   == TLCFP(kSubset(4, 1..3)) = TLCFP({})
FPKSubsetNegativeEqEmpty   == TLCFP(kSubset(-1, 1..3)) = TLCFP({})
FPKTwoFourEqDefinition     == TLCFP(K24) = TLCFP(D24)
FPKTwoFourSymEqDefinition  == TLCFP(K24Sym) = TLCFP(D24)
FPKThreeFourEqDefinition   == TLCFP(K34) = TLCFP(D34)
FPKThreeFourSymEqDefinition == TLCFP(K34Sym) = TLCFP(D34)
FPKThreeFiveEqDefinition   == TLCFP(K35) = TLCFP(D35)
FPKThreeFiveSymEqDefinition == TLCFP(K35Sym) = TLCFP(D35)
FPPairKTwoEightKOneFiveOrderIndependent == TLCFP({K28, K15}) = TLCFP({K15, K28})
FPPairKThreeSixKOneTwentyOrderIndependent == TLCFP({K36, K120}) = TLCFP({K120, K36})
FPMixedEqEnums             == TLCFP({K1, K2, E1, E2}) = TLCFP({E1, E2})
FPMixedEqEnumsRev          == TLCFP({E2, E1, K2, K1}) = TLCFP({E2, E1})
FPMixedOrderIndependent    == TLCFP({K1, K2, E1, E2}) = TLCFP({E2, E1, K2, K1})

-----------------------------------------------------------------------------
\* A base set that no enumeration of its k-subsets fits in.

KSubsetLargeFinite              == IsFiniteSet(kSubset(2, 1..64))
PairInKSubsetLarge              == {1, 2} \in kSubset(2, 1..64)
CardKSubsetLarge                == Cardinality(kSubset(2, 1..64)) = 2016
CardKSubsetAllLarge             == Cardinality(kSubset(64, 1..64)) = 1
CardKSubsetAllButOneLarge       == Cardinality(kSubset(63, 1..64)) = 64
CardKSubsetAllMaxEnumerable     == Cardinality(kSubset(63, 1..63)) = 1
CardKSubsetAllMillion           == Cardinality(kSubset(1000000, 1..1000000)) = 1
CardKSubsetAllButOneMillion     == Cardinality(kSubset(999999, 1..1000000)) = 1000000
CardKSubsetMiddleLargeReflexive == Cardinality(kSubset(32, 1..64)) = Cardinality(kSubset(32, 1..64))
CardPairK31K32Large             == Cardinality({kSubset(31, 1..64), kSubset(32, 1..64)}) = 2
CardPairK32K31Large             == Cardinality({kSubset(32, 1..64), kSubset(31, 1..64)}) = 2
CardPairK31LargeK2Small         == Cardinality({kSubset(31, 1..64), kSubset(2, 1..10)}) = 2
CardPairK2SmallK31Large         == Cardinality({kSubset(2, 1..10), kSubset(31, 1..64)}) = 2
KSubsetLargeDiffPowerSet        == kSubset(2, 1..64) # SUBSET (1..64)
PowerSetLargeDiffKSubset        == SUBSET (1..64) # kSubset(2, 1..64)
CardPairKSubsetPowerSetLarge    ==
  Cardinality({kSubset(2, 1..64), SUBSET (1..64)}) = 2
CardPairPowerSetKSubsetLarge    ==
  Cardinality({SUBSET (1..64), kSubset(2, 1..64)}) = 2
=============================================================================
