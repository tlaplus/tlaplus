------------------------ MODULE ValueSemanticsAssume ------------------------
\* TLC checks each shared proposition as a startup assumption. A false result
\* is a semantic disagreement with ValueSemanticsTheorems.tla.
EXTENDS FiniteSets, Integers, Sequences, TLC, TLCExt

CONSTANT Model

INSTANCE ValueSemanticsCases WITH Fingerprint <- TLCFP,
                                  Combine <- LAMBDA f, g : f @@ g

ASSUME IntReflexive
ASSUME IntNestedDuplicate
ASSUME StringReflexive
ASSUME StringNestedDuplicate
ASSUME BoolReflexive
ASSUME BoolNestedDuplicate
ASSUME ModelReflexive
ASSUME ModelNestedDuplicate

ASSUME EnumPermutation
ASSUME EnumDuplicates
ASSUME EnumMember
ASSUME EnumNotMember
ASSUME CardEnum
ASSUME FiniteEnum
ASSUME FPEnumPermutation

ASSUME IntervalEqEnum
ASSUME EnumEqInterval
ASSUME IntervalNested
ASSUME IntervalDuplicate
ASSUME IntervalMember
ASSUME IntervalNotMember
ASSUME CardInterval
ASSUME FiniteInterval
ASSUME FPIntervalEnum

ASSUME SubsetEqEnum
ASSUME EnumEqSubset
ASSUME SubsetNested
ASSUME SubsetBaseDuplicate
ASSUME SubsetBaseDuplicateNested
ASSUME SubsetMember
ASSUME SubsetNotMember
ASSUME CardSubset
ASSUME FiniteSubset
ASSUME FPSubsetEnum

ASSUME CapEqEnum
ASSUME EnumEqCap
ASSUME CapNested
ASSUME CapSym
ASSUME CapSymNested
ASSUME CapMember
ASSUME CapNotMember
ASSUME CardCap
ASSUME FiniteCap
ASSUME FPCapEnum

ASSUME DiffEqEnum
ASSUME EnumEqDiff
ASSUME DiffNested
ASSUME DiffSameEmpty
ASSUME DiffSameNested
ASSUME LazyDiffEqEnum
ASSUME LazyDiffMember
ASSUME LazyDiffNotMember
ASSUME CardLazyDiff
ASSUME FiniteLazyDiff
ASSUME FPLazyDiffEnum

ASSUME CupEqEnum
ASSUME EnumEqCup
ASSUME CupNested
ASSUME CupSym
ASSUME CupSymNested
ASSUME LazyCupEqEnum
ASSUME LazyCupMember
ASSUME LazyCupNotMember
ASSUME CardLazyCup
ASSUME FiniteLazyCup
ASSUME FPLazyCupEnum

ASSUME UnionPower
ASSUME UnionPowerRev
ASSUME UnionPowerNested
ASSUME UnionDuplicate
ASSUME UnionMember
ASSUME UnionNotMember
ASSUME CardUnion
ASSUME FiniteUnion
ASSUME FPUnionEnum

ASSUME PredEqEnum
ASSUME EnumEqPred
ASSUME PredNested
ASSUME PredAll
ASSUME PredAllNested
ASSUME PredMember
ASSUME PredNotMember
ASSUME CardPred
ASSUME FinitePred
ASSUME FPPredEnum

ASSUME FcnEqRecord
ASSUME RecordEqFcn
ASSUME FcnRecordNested
ASSUME FcnEqTuple
ASSUME TupleEqFcn
ASSUME FcnTupleNested
ASSUME RecordEqTupleFunction
ASSUME FcnDomain
ASSUME FcnApply
ASSUME RecordDomain
ASSUME RecordApply
ASSUME TupleDomain
ASSUME TupleApply
ASSUME FPFcnRecord
ASSUME FPFcnTuple
ASSUME LazySetEquality
ASSUME LazySetNested
ASSUME LazyFcnApplication

ASSUME FcnExceptSame
ASSUME FcnExceptUpdate
ASSUME TupleExceptSame
ASSUME TupleExceptUpdate
ASSUME RecordExceptSame
ASSUME RecordExceptUpdate
ASSUME FPFcnExceptSame
ASSUME FPTupleExceptSame
ASSUME FPRecordExceptSame
ASSUME FcnExceptMissing
ASSUME TupleExceptMissing
ASSUME RecordExceptMissing
ASSUME NestedFcnExcept
ASSUME NestedTupleExcept
ASSUME NestedRecordExcept
ASSUME FcnExceptAt
ASSUME TupleExceptAt
ASSUME RecordExceptAt
ASSUME NestedExceptMissing
ASSUME FcnExceptLastWins
ASSUME FcnExceptAtNested
ASSUME TupleExceptLastWins
ASSUME FcnCombineDisjoint
ASSUME FcnCombineLeftWins
ASSUME IntervalFcnCombine
ASSUME IntervalEmptySubsetEmpty
ASSUME IntervalEmptySubsetEnum
ASSUME IntervalEmptySubsetNat
ASSUME IntervalNotSubsetEmpty
ASSUME EmptyIntervalsNested
ASSUME FPEmptyIntervals
ASSUME EmptyIntervalFcnEqTuple
ASSUME EmptyEnumFcnEqTuple
ASSUME EmptyTupleEqIntervalFcn
ASSUME EmptyIntervalFcnsEq
\* ASSUME EmptyIntervalFcnsNested
\* ASSUME EmptyIntervalFcnsSetEq
ASSUME NegativeEmptyIntervalFcnEqTuple
\* ASSUME EmptyTupleEqNegativeIntervalFcn(0)
\* ASSUME EmptyIntervalFcnNested
ASSUME EmptyEnumFcnNested
ASSUME EmptyFcnDomainsNested
\* ASSUME EmptyFcnNested
\* ASSUME EmptyFcnSetEqSingleton
ASSUME EmptyFcnSetPermutation
ASSUME ChooseEmptyFcnSet
ASSUME FPEmptyFcnTuple
\* ASSUME FPMixedEmptyFcnSet
\* ASSUME CardSubsetMixedEmptyFcn
\* ASSUME SubsetMixedEmptyFcnEq
\* ASSUME CardCupMixedEmptyFcn
\* ASSUME CardUnionMixedEmptyFcn
\* ASSUME CardFcnSetMixedEmptyFcn
\* ASSUME CardRcdSetMixedEmptyFcn
\* ASSUME CardTupleSetMixedEmptyFcn
ASSUME EmptyIntervalBodiesEq
ASSUME EmptyZeroIntervalFcnEqTuple
ASSUME EmptyCanonicalVsOtherInterval
\* ASSUME EmptyIntervalBodiesNested
\* ASSUME EmptyCanonicalVsOtherNested
\* ASSUME EmptyFcnSingletonEq
ASSUME EmptyFcnDomainEq
ASSUME EmptyFcnExceptNoop
ASSUME NestedEmptyFcnEq
\* ASSUME NestedEmptyFcnNested
ASSUME NestedEmptyRecordEq
\* ASSUME NestedEmptyRecordNested
ASSUME NestedEmptyTupleEq
\* ASSUME NestedEmptyTupleNested
ASSUME FPEmptyIntervalFcns
ASSUME LenEmptyEnumFcn
ASSUME LenCanonicalEmptyFcn
ASSUME AppendCanonicalEmptyFcn
ASSUME EmptyEnumFcnInSeqEmpty

ASSUME FcnSetEqEnum
ASSUME FcnSetEqEnumRev
ASSUME FcnSetNested
ASSUME FcnSetMember
ASSUME FcnSetNotMember
ASSUME CardFcnSet
ASSUME FiniteFcnSet
ASSUME FPFcnSetEnum
ASSUME EmptyDomainFcnSetEq
ASSUME EmptyDomainFcnSetSingleton
ASSUME EmptyIntervalDomainFcnSetEq
ASSUME CardSingletonRangeNat
ASSUME FiniteSingletonRangeNat
ASSUME EmptyFcnInEmptyDomainSet
ASSUME EmptyRangeNatEqEmpty
ASSUME CardEmptyRangeNat
ASSUME FiniteEmptyRangeNat
ASSUME EmptyRangeFcnSetSingleton
ASSUME EmptyFcnInEmptyRangeSet
ASSUME NatZeroFcnApply
ASSUME NatZeroFcnDomain
ASSUME NatExceptApply
ASSUME NatExceptOrig
ASSUME NatExceptAt
ASSUME NatExceptDomain
ASSUME BoolZeroFcnMember
ASSUME BoolZeroFcnForall
ASSUME FcnSetBoolSingleton
ASSUME ChooseBoolFcn
ASSUME CardBoolFcnSet
ASSUME StringZeroApply
ASSUME FcnSetNatCupEmpty
ASSUME FcnSetRangeCupEmpty
ASSUME EmptyRangeSTRING
ASSUME CardEmptyRangeSTRING
ASSUME FiniteEmptyRangeSTRING
ASSUME CardSingletonRangeSeqEmpty
ASSUME FiniteSeqEmptyFcnSet

ASSUME RcdSetEqEnum
ASSUME RcdSetEqEnumRev
ASSUME RcdSetNested
ASSUME RcdSetMember
ASSUME RcdSetNotMember
ASSUME CardRcdSet
ASSUME FiniteRcdSet
ASSUME FPRcdSetEnum
ASSUME EmptyRcdFieldEqEmpty
ASSUME EmptyRcdFieldNatEqEmpty
ASSUME FiniteEmptyRcdFieldNat
ASSUME RcdSetNatCupEmpty
ASSUME FiniteSeqEmptyRcdSet
ASSUME RcdNatMember
ASSUME RcdSetBoolEq
ASSUME RcdSetBoolMember
ASSUME CardRcdSetBool
ASSUME FiniteRcdSetBool
ASSUME RcdSetBoolFieldEq

ASSUME TupleSetEqEnum
ASSUME TupleSetEqEnumRev
ASSUME TupleSetNested
ASSUME TupleSetMember
ASSUME TupleSetNotMember
ASSUME CardTupleSet
ASSUME FiniteTupleSet
ASSUME FPTupleSetEnum
ASSUME TupleSetEqFcnSet
ASSUME EmptyProductEq
ASSUME EmptyProductEmpty
ASSUME FiniteEmptyProduct
ASSUME CardEmptyProduct
ASSUME EmptyProductIn
ASSUME NestedProductNeqNary
ASSUME NaryProductMember
ASSUME NestedProductNotInNary
ASSUME NaryProductEqEnum
ASSUME FiniteSeqEmptyProduct
ASSUME TupleInSeq
ASSUME FcnInSeq

ASSUME IntCapEnum
ASSUME StringCapEnum
ASSUME SeqCapEnum
ASSUME FPIntCapEnum
ASSUME FPStringCapEnum
ASSUME FPSeqCapEnum
ASSUME EmptySeqInSeqEmpty
ASSUME FiniteSeqEmpty
ASSUME EnumSubsetSeqEmpty
ASSUME SeqCapEmptyEnum
ASSUME SeqCupEmpty
ASSUME EmptyInUnionSeq
ASSUME EmptyInSubsetSeq
ASSUME SingletonInSubsetSeq
ASSUME FiniteSubsetSeqEmpty
ASSUME EmptyStringInSTRING
ASSUME EnumSubsetNat
ASSUME EnumSubsetInt
ASSUME NatCupEmptyEqNat
ASSUME NatPairCupEmpty
ASSUME ZeroInNatCupZero
ASSUME EnumSubsetNatCupZero
ASSUME OneInNatDiffZero
ASSUME ZeroNotInNatDiffZero
ASSUME EnumSubsetNatDiff
ASSUME ZeroInPredNat
ASSUME BoolMember
ASSUME BoolEqEnum
ASSUME CardBool
ASSUME FiniteBool
ASSUME ChooseBool
ASSUME BoolSubsetEnum
ASSUME EnumSubsetBool
ASSUME BoolPredTrue
ASSUME CardBoolPredTrue
ASSUME SubsetBoolEq
ASSUME CardSubsetBool
ASSUME FPBoolEnum
ASSUME EmptyInSeqOne
ASSUME EnumSubsetSeqOne
ASSUME EmptyInSeqCap
ASSUME FiniteSeqCapEmptyOne
ASSUME ZeroInNatCapNat
ASSUME EmptyInStringCap
ASSUME PairInNatProduct
ASSUME EnumSubsetNatProduct
ASSUME CaseTrue
ASSUME CaseOther
ASSUME BoolPredFalse
ASSUME BoolIdApply
ASSUME RcdDomain
ASSUME RcdExcept
ASSUME TupleInSeqNat
ASSUME OneInIntCapNat
ASSUME EnumInSubsetNat
ASSUME LenTuple
ASSUME SubsetSingleton
ASSUME EmptyNeqString
ASSUME ChooseSingleton
ASSUME EmptyInSeqCapDisjoint
ASSUME BoolCupTrue
ASSUME TrueCupBool
ASSUME UnionBool
ASSUME BoolSubsetSelf
ASSUME FourInBoundedPred
ASSUME FiveNotInBoundedPred
ASSUME EnumSubsetBoundedPred
ASSUME ZeroNotInNatDiffNat
ASSUME FiniteEnumDiffNat
ASSUME EnumDiffNatEmpty
ASSUME ThreeInIntervalCapNat
ASSUME FiniteIntervalCapNat
ASSUME IntervalCapNatEq
ASSUME FinitePredOverEnum
ASSUME PredOverEnumEq
ASSUME CardStringSingletonRange
ASSUME FiniteStringSingletonRange
ASSUME FcnDomainOrder
ASSUME NestedRcdExcept
ASSUME ConcatEmptyRight
ASSUME DivPos
ASSUME ModPos
ASSUME UnionIntervals
ASSUME CardNatIntPair
ASSUME NatIntSetPerm
ASSUME HeadTuple
ASSUME TailSingleton
ASSUME AppendEmpty
ASSUME ConcatTuples
ASSUME SubSeqEmpty
ASSUME LenEmptyTuple
ASSUME NegEmptyInterval
ASSUME CardNegEmptyInterval
ASSUME LambdaExcept
ASSUME DivNegDividend
ASSUME ModNegDividend
ASSUME FiniteNatCapEmpty
ASSUME FiniteEmptyDiffNat
ASSUME OneInUnionNat
ASSUME VacuousForall
ASSUME EmptyExists

ASSUME RecordPermutation
ASSUME TupleReflexive
ASSUME TupleDomainDiffer
ASSUME IntervalReflexive
ASSUME IntervalDiffer
ASSUME SubsetIntervalEq
ASSUME SubsetIntervalEqRev
ASSUME CapLazyEqEnum
ASSUME CupLazyEqEnum
ASSUME DiffLazyEqEnum
ASSUME UnionLazyEqEnum
ASSUME PredEquivalent
ASSUME FcnSetStructuralEq
ASSUME FcnSetStructuralDiff
ASSUME RcdSetPermutation
ASSUME TupleSetStructuralEq
ASSUME NatDiffInt
ASSUME IntDiffNat
ASSUME StringInStringSet

ASSUME EnumQuantifiers
ASSUME IntervalQuantifiers
ASSUME SubsetQuantifiers
ASSUME CapQuantifiers
ASSUME DiffQuantifiers
ASSUME CupQuantifiers
ASSUME UnionQuantifiers
ASSUME PredQuantifiers
ASSUME FcnSetQuantifiers
ASSUME RcdSetQuantifiers
ASSUME TupleSetQuantifiers
ASSUME ChooseIntervalEnum
ASSUME ChooseSubsetEnum
ASSUME ChooseCapEnum
ASSUME ChooseDiffEnum
ASSUME ChooseCupEnum
ASSUME ChooseUnionEnum
ASSUME ChoosePredEnum
ASSUME ChooseFcnSetEnum
ASSUME ChooseRcdSetEnum
ASSUME ChooseTupleSetEnum
ASSUME MaxIntervalExists
ASSUME MaxIntervalForall
ASSUME MaxIntervalChoose
ASSUME MaxIntervalEqEnum
ASSUME MaxEnumSubsetInterval
ASSUME MaxIntervalReflexiveSubset
ASSUME CardMaxIntervalPair
ASSUME CardSubsetMaxInterval
ASSUME MaxIntervalFcnApply
ASSUME CardMaxInterval
ASSUME MaxIntInMaxInterval
ASSUME MinIntNotInMaxInterval
ASSUME EmptyInSubsetMax
ASSUME MaxSingletonInSubsetMax
ASSUME MinSingletonNotInSubsetMax
ASSUME MinIntInSingleton
ASSUME CardMinInterval
ASSUME MinIntervalEq
ASSUME MixedEmptyFcnApplyTuple
ASSUME MixedEmptyFcnApplyInterval

ASSUME BoundaryIntervalFcnSetPermutation
ASSUME BoundaryMixedFcnSetPermutation
ASSUME BoundaryFcnDomainNormalize
ASSUME BoundaryFcnSelect
ASSUME BoundaryFcnExcept
ASSUME BoundaryFcnBinarySelect
ASSUME FPBoundaryFcns

-----------------------------------------------------------------------------
\* TLAPS proves every proposition below in ValueSemanticsTheorems.  Wrong
\* Booleans and runaway evaluations stay commented so one case does not hide
\* the others.  The refusals that follow are AssertError assumptions: giving
\* up is acceptable, whereas a wrong answer is not.

ASSUME MaxIntervalSubset(0)
ASSUME MaxIntervalDiff(0)
ASSUME MaxIntervalCap(0)
ASSUME MaxIntervalCup(0)
ASSUME MaxIntervalPred(0)
ASSUME FPMaxInterval(0)

\* Infinite empty results that TLC attempts to enumerate indefinitely.
\* ASSUME InfiniteCapEmpty(0)
\* ASSUME InfiniteDiffEmpty(0)
\* ASSUME InfinitePredEmpty(0)

ASSUME MaxIntervalFcnEq(0)
ASSUME MaxIntervalFcnMember(0)
ASSUME MaxIntervalFcnCombine(0)
ASSUME MaxIntervalFcnCombineRev(0)
ASSUME MaxPredExists(0)
ASSUME MaxPredForall(0)
ASSUME MaxCapExists(0)
ASSUME MaxCupExists(0)
ASSUME MaxDiffExists(0)
ASSUME MaxUnionExists(0)
ASSUME MaxTupleSetExists(0)
ASSUME MaxRcdSetExists(0)
ASSUME MaxFcnSetExists(0)

\* Application of the mixed empty-domain function succeeds, but TLC keeps both
\* equal keys in the constructed DOMAIN, so extensional equality fails.
\* ASSUME MixedEmptyFcnEq(0)
\* ASSUME MixedEmptyFcnDomainEq(0)
\* ASSUME MixedEmptyFcnDomainCard(0)

-----------------------------------------------------------------------------
\* Mathematically finite empty results that TLC refuses to classify as finite.
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to check if expression of form {x \\in S : p(x)} is a finite set, but cannot check if S:\nNat\nis finite.",
                   FiniteInfinitePredEmpty(0))
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to check if expression of form {x \\in S : p(x)} is a finite set, but cannot check if S:\nNat\nis finite.",
                   FiniteCupInfinitePredEmpty(0))
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to check if expression of form {x \\in S : p(x)} is a finite set, but cannot check if S:\nNat\nis finite.",
                   FiniteUnionInfinitePredEmpty(0))

\* Only an interval domain whose lower bound is 1 is converted to a tuple, so
\* the Sequences operators refuse the empty function that TLC prints as <<>>.
ASSUME AssertError("The argument of Len should be a sequence, but instead it is:\n<<>>",
                   LenEmptyIntervalFcn(0))
ASSUME AssertError("Evaluating an expression of the form Append(s, v) when s is not a sequence:\n<<>>",
                   AppendEmptyIntervalFcn(0))
ASSUME AssertError("Evaluating an expression of the form s \\o t when s is not a sequence:\n<<>>",
                   ConcatEmptyIntervalFcn(0))
ASSUME AssertError("Attempted to check if the value:\n<<>>\nis an element of Seq({}).",
                   EmptyIntervalFcnInSeqEmpty(0))

\* Seq({}) is finite and equal to {<<>>}, but UserValue comparison and size
\* refuse the explicit singleton.
ASSUME AssertError("Attempted to compare overridden value Seq({}) with non-overridden value:\n{<<>>}",
                   SeqEmptyEq(0))
ASSUME AssertError("Attempted to compute cardinality of the value\nSeq({})",
                   CardSeqEmpty(0))
\* The same UserValue is not Enumerable and has no size(), so subset,
\* quantification, UNION, and derived cardinalities fail.
ASSUME AssertError("Attempted to evaluate an expression of form S \\subseteq T, but S was not enumerable.\nline 614, col 33 to line 614, col 57 of module ValueSemanticsCases",
                   SeqEmptySubsetSelf(0))
ASSUME AssertError("Attempted to evaluate an expression of form S \\subseteq T, but S was not enumerable.\nline 615, col 33 to line 615, col 56 of module ValueSemanticsCases",
                   SeqEmptySubsetEnum(0))
ASSUME AssertError("TLC encountered the non-enumerable quantifier bound\nSeq({})\nline 616, col 42 to line 616, col 48 of module ValueSemanticsCases\nIn TLA+, Seq(S) represents the set of all finite sequences whose elements come from the set S. Even when S\nis a finite set, the number of possible sequences in Seq(S) is unbounded because sequences can have any\nfinite length (e.g., length 0, 1, 2, and so on). As a result, TLC cannot evaluate expressions that\nuniversally (\\A) or existentially (\\E) quantify over Seq({}), because this would require checking an\ninfinite number of cases. Note that for a finite set of sequences s, TLC handles s \\subseteq Seq(S).\nSee https://explain.tlapl.us/seq-unenumerable for additional details.",
                   SeqEmptyExists(0))
ASSUME AssertError("Attempted to enumerate UNION(s), but some element of s is nonenumerable.",
                   UnionSeqEmpty(0))
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to compute the number of elements in the overridden value Seq({}).",
                   CardSeqEmptyProduct(0))
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to compute the number of elements in the overridden value Seq({}).",
                   CardSeqEmptyFcnSet(0))
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to compute the number of elements in the overridden value Seq({}).",
                   CardSeqEmptyRcdSet(0))
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to compute the number of elements in the overridden value Seq({}).",
                   CardSubsetSeqEmpty(0))
\* SetCupValue / SetPredValue equality enumerates, and UserValue is not
\* Enumerable, so extensional identities over Nat are refused.
ASSUME AssertError("Attempted to enumerate S \\cup T when S:\n{0}\nand T:\nNat\nare not both enumerable",
                   NatCupZeroEqNat(0))
\* Reflexive equality of a lazy infinite union, difference, or UNION
\* also enumerates instead of succeeding.
ASSUME AssertError("Attempted to enumerate S \\cup T when S:\n{0}\nand T:\nNat\nare not both enumerable",
                   NatCupZeroRefl(0))
ASSUME AssertError("Attempted to enumerate { x \\in S : p(x) } when S:\nNat\nis not enumerable",
                   PredNatEqNat(0))
ASSUME AssertError("Attempted to evaluate an expression of form S \\subseteq T, but S was not enumerable.\nline 626, col 29 to line 626, col 45 of module ValueSemanticsCases",
                   NatSubsetNat(0))
ASSUME AssertError("Attempted to enumerate S \\ T when S:\nNat\nis not enumerable.",
                   NatDiffZeroRefl(0))
ASSUME AssertError("Attempted to enumerate UNION(s), but some element of s is nonenumerable.",
                   UnionNatEqNat(0))
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to enumerate S \\cup T when S:\n{0}\nand T:\nNat\nare not both enumerable",
                   NatPairCupZero(0))
\* [Nat -> {0}] is a singleton, but membership and quantification convert
\* or enumerate the infinite domain.
ASSUME AssertError("Attempted to compute the number of elements in the overridden value Nat.",
                   NatZeroFcnMember(0))
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the domain D:\nNat\ncannot be enumerated.",
                   NatZeroFcnForall(0))
ASSUME AssertError("Attempted to enumerate S \\cup T when S:\n{0}\nand T:\nNat\nare not both enumerable",
                   FcnSetNatCupZero(0))
\* Application and DOMAIN of EXCEPT on Nat succeed; extensional equality
\* converts the function and enumerates the infinite domain.
ASSUME AssertError("Attempted to compute the number of elements in the overridden value Nat.",
                   NatExceptExt(0))
\* UserValue.compareTo refuses a finite set, so inequality with {1} or
\* {} errors even though a membership witness is immediate.
ASSUME AssertError("Attempted to compare overridden value Nat with non-overridden value:\n{1}",
                   NatNeqSingleton(0))
ASSUME AssertError("Attempted to check equality of the set {} with the value:\nNat",
                   EmptyNeqNat(0))
\* Intersection of two UserValues is refused even when the result is
\* {<<>>} or Nat.
ASSUME AssertError("Attempted to enumerate S \\cap T when neither S:\nSeq({})\nnor T:\nSeq({1})\nis enumerable",
                   SeqCapEmptyOneEq(0))
ASSUME AssertError("Attempted to enumerate S \\cap T when neither S:\nNat\nnor T:\nNat\nis enumerable",
                   NatCapNatEq(0))
\* Seq({1}) is a subset of Seq({1,2}), but UserValue is not Enumerable.
ASSUME AssertError("Attempted to evaluate an expression of form S \\subseteq T, but S was not enumerable.\nline 642, col 32 to line 642, col 61 of module ValueSemanticsCases",
                   SeqOneSubsetSeqTwo(0))
\* Seq({1}) \cap Seq({2}) is {<<>>}; membership succeeds, but IsFiniteSet
\* and equality refuse a cap of two non-enumerable sequence sets.
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to check if the set Seq({1}) \\cap Seq({2})is finite.",
                   FiniteSeqCapDisjoint(0))
ASSUME AssertError("Attempted to enumerate S \\cap T when neither S:\nSeq({1})\nnor T:\nSeq({2})\nis enumerable",
                   SeqCapDisjointEq(0))
\* Nat \subseteq Int and Int \cap Nat = Nat are true, but UserValue is
\* not Enumerable and SetCapValue will not intersect two infinite sets.
ASSUME AssertError("Attempted to evaluate an expression of form S \\subseteq T, but S was not enumerable.\nline 647, col 26 to line 647, col 42 of module ValueSemanticsCases",
                   NatSubsetInt(0))
ASSUME AssertError("Attempted to enumerate S \\cap T when neither S:\nInt\nnor T:\nNat\nis enumerable",
                   IntCapNatEq(0))
\* UserValue.compareTo refuses a finite set, so STRING # {""} errors.
ASSUME AssertError("Attempted to compare overridden value STRING with non-overridden value:\n{\"\"}",
                   StringNeqEmpty(0))
\* {x \in Nat : x < 5} is 0..4.  Membership and a finite left-hand subset
\* succeed; IsFiniteSet, Cardinality, quantification, and equality refuse
\* the non-enumerable carrier.
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to check if expression of form {x \\in S : p(x)} is a finite set, but cannot check if S:\nNat\nis finite.",
                   FiniteBoundedPred(0))
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to enumerate { x \\in S : p(x) } when S:\nNat\nis not enumerable",
                   CardBoundedPred(0))
ASSUME AssertError("Attempted to enumerate { x \\in S : p(x) } when S:\nNat\nis not enumerable",
                   ExistsBoundedPred(0))
ASSUME AssertError("Attempted to enumerate { x \\in S : p(x) } when S:\nNat\nis not enumerable",
                   BoundedPredEq(0))
\* Nat \ Nat is empty, but both-infinite SetDiffValue.isFinite errors.
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to check if the set Nat \\ Natis finite.",
                   FiniteNatDiffNat(0))
\* [STRING -> {0}] is a singleton, but membership converts the function.
ASSUME AssertError("Attempted to compute the number of elements in the overridden value STRING.",
                   StringZeroFcnMember(0))
=============================================================================
