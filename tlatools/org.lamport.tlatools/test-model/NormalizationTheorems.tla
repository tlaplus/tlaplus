------------------------ MODULE NormalizationTheorems ------------------------
\* Representation-independent proofs of the propositions that
\* NormalizationAssume.tla asks TLC to evaluate.
EXTENDS FiniteSets, FiniteSetTheorems, Integers, Sequences, TLAPS

CONSTANTS TypedA, TypedB

\* The operators of the TLC module as that module defines them, because tlapm
\* cannot load it.
Cases == INSTANCE NormalizationCases
  WITH IsFiniteSet <- IsFiniteSet, TypedA <- TypedA, TypedB <- TypedB,
       RandomElement <- LAMBDA s : CHOOSE x \in s : TRUE,
       ToString <- LAMBDA v : (CHOOSE x \in [a : v, b : STRING] : TRUE).b,
       Print <- LAMBDA out, val : val,
       TLCEval <- LAMBDA v : v,
       Assert <- LAMBDA val, out : IF val = TRUE THEN TRUE
                                   ELSE CHOOSE v : TRUE,
       :> <- LAMBDA d, e : [x \in {d} |-> e],
       @@ <- LAMBDA f, g : [x \in (DOMAIN f) \cup (DOMAIN g) |->
                              IF x \in DOMAIN f THEN f[x] ELSE g[x]]

THEOREM MixedMember == Cases!MixedMember
  BY DEF Cases!MixedMember

THEOREM MixedFcnApply == Cases!MixedFcnApply
  BY DEF Cases!MixedFcnApply

THEOREM MixedFcnExcept == Cases!MixedFcnExcept
  BY DEF Cases!MixedFcnExcept

THEOREM MixedCupEmptyMember == Cases!MixedCupEmptyMember
  BY DEF Cases!MixedCupEmptyMember

THEOREM FiniteMixed == Cases!FiniteMixed
  <1>1. IsFiniteSet({"a"})
    BY FS_Singleton
  <1>2. IsFiniteSet({"a"} \cup {1})
    BY <1>1, FS_AddElement
  <1>3. {"a"} \cup {1} = {1, "a"}
    OBVIOUS
  <1>4. QED BY <1>2, <1>3 DEF Cases!FiniteMixed

THEOREM TypedMember == Cases!TypedMember
  BY DEF Cases!TypedMember

THEOREM TypedIntMember == Cases!TypedIntMember
  BY DEF Cases!TypedIntMember

THEOREM TypedStringMember == Cases!TypedStringMember
  BY DEF Cases!TypedStringMember

THEOREM IntTypedMember == Cases!IntTypedMember
  BY DEF Cases!IntTypedMember

THEOREM MixedBoundMember == Cases!MixedBoundMember
  BY DEF Cases!MixedBoundMember

THEOREM LazyFcnExceptDomain == Cases!LazyFcnExceptDomain
  BY DEF Cases!LazyFcnExceptDomain

THEOREM LazyFcnInTuple == Cases!LazyFcnInTuple
  BY DEF Cases!LazyFcnInTuple

THEOREM LazyPredFcnSetNeqEmpty == Cases!LazyPredFcnSetNeqEmpty
  <1>1. [x \in {1} |-> {1, "a"}] \in [{1} -> {{1, "a"}}]
    OBVIOUS
  <1>2. QED BY <1>1 DEF Cases!LazyPredFcnSetNeqEmpty

THEOREM LazyPredSubsetNeqEmpty == Cases!LazyPredSubsetNeqEmpty
  <1>1. {{1, "a"}} \in SUBSET {{1, "a"}} /\ {{1, "a"}} # {}
    OBVIOUS
  <1>2. QED BY <1>1 DEF Cases!LazyPredSubsetNeqEmpty

THEOREM TupleApplyMixed == Cases!TupleApplyMixed
  BY DEF Cases!TupleApplyMixed

THEOREM HeadMixed == Cases!HeadMixed
  BY DEF Cases!HeadMixed

THEOREM TailMixed == Cases!TailMixed
  BY DEF Cases!TailMixed

THEOREM AppendMixed == Cases!AppendMixed
  BY DEF Cases!AppendMixed

THEOREM ConcatMixed == Cases!ConcatMixed
  BY DEF Cases!ConcatMixed

THEOREM SubSeqMixed == Cases!SubSeqMixed
  BY DEF Cases!SubSeqMixed

THEOREM RcdFieldMixed == Cases!RcdFieldMixed
  BY DEF Cases!RcdFieldMixed

THEOREM RcdDomainMixed == Cases!RcdDomainMixed
  BY DEF Cases!RcdDomainMixed

THEOREM TupleEnumMember == Cases!TupleEnumMember
  BY DEF Cases!TupleEnumMember

THEOREM RcdEnumMember == Cases!RcdEnumMember
  BY DEF Cases!RcdEnumMember

THEOREM FcnEnumMember == Cases!FcnEnumMember
  BY DEF Cases!FcnEnumMember

THEOREM SetEnumMember == Cases!SetEnumMember
  BY DEF Cases!SetEnumMember

THEOREM SubsetMixedMember == Cases!SubsetMixedMember
  BY DEF Cases!SubsetMixedMember

THEOREM SubsetMixedCupMember == Cases!SubsetMixedCupMember
  BY DEF Cases!SubsetMixedCupMember

THEOREM SeqMixedMember == Cases!SeqMixedMember
  BY DEF Cases!SeqMixedMember

THEOREM ProductMixedMember == Cases!ProductMixedMember
  BY DEF Cases!ProductMixedMember

THEOREM ProductEmptyRight == Cases!ProductEmptyRight
  BY DEF Cases!ProductEmptyRight

THEOREM ProductEmptyLeft == Cases!ProductEmptyLeft
  BY DEF Cases!ProductEmptyLeft

THEOREM ProductEmptyEq == Cases!ProductEmptyEq
  BY DEF Cases!ProductEmptyEq

THEOREM FcnSetMixedMember == Cases!FcnSetMixedMember
  BY DEF Cases!FcnSetMixedMember

THEOREM RcdSetMixedMember == Cases!RcdSetMixedMember
  BY DEF Cases!RcdSetMixedMember

THEOREM MixedMemberSecond == Cases!MixedMemberSecond
  BY DEF Cases!MixedMemberSecond

THEOREM MixedPredMember == Cases!MixedPredMember
  BY DEF Cases!MixedPredMember

THEOREM MixedCapMember == Cases!MixedCapMember
  BY DEF Cases!MixedCapMember

THEOREM MixedDiffMember == Cases!MixedDiffMember
  BY DEF Cases!MixedDiffMember

THEOREM MixedCupMember == Cases!MixedCupMember
  BY DEF Cases!MixedCupMember

THEOREM UnionMixedMember == Cases!UnionMixedMember
  BY DEF Cases!UnionMixedMember

THEOREM UnionMixedSingleton == Cases!UnionMixedSingleton
  BY DEF Cases!UnionMixedSingleton

THEOREM MixedSubseteq == Cases!MixedSubseteq
  BY DEF Cases!MixedSubseteq

THEOREM MixedNeqEmpty == Cases!MixedNeqEmpty
  BY DEF Cases!MixedNeqEmpty

THEOREM EmptyNeqMixed == Cases!EmptyNeqMixed
  BY DEF Cases!EmptyNeqMixed

THEOREM FcnRangeMixedNeqEmpty == Cases!FcnRangeMixedNeqEmpty
  BY DEF Cases!FcnRangeMixedNeqEmpty

THEOREM MixedDomainMember == Cases!MixedDomainMember
  BY DEF Cases!MixedDomainMember

THEOREM MixedFcnEq == Cases!MixedFcnEq
  BY DEF Cases!MixedFcnEq

THEOREM MixedFcnSetMember == Cases!MixedFcnSetMember
  BY DEF Cases!MixedFcnSetMember

THEOREM SeqMixedPairMember == Cases!SeqMixedPairMember
  BY DEF Cases!SeqMixedPairMember

THEOREM ProductEmptyNonTuple == Cases!ProductEmptyNonTuple
  BY DEF Cases!ProductEmptyNonTuple

\* No theorem states the following propositions, because TLA+ determines
\* neither them nor their negations:
\*  - SelectSeqMixed: TLA+ doesn't say whether {1, "a"} = 1, which decides
\*    whether SelectSeq keeps the second element.
\*  - SubsetFcnSetMember: TLA+ doesn't say whether 1 \in SUBSET {1, "a"},
\*    i.e. what the elements of 1 are.
\*  - ToStringRcd, ToStringRcdOrder, ToStringFcnOrder: the TLC module defines
\*    ToString(v) to be some string, not the string TLC prints.
\*  - AssertRcdOrder, AssertFcnOrder: the TLC module defines Assert(FALSE, out)
\*    to be some value.

THEOREM RandomElementMixed == Cases!RandomElementMixed
  BY DEF Cases!RandomElementMixed

THEOREM ToStringMixed == Cases!ToStringMixed
  <1>1. [a |-> 1, b |-> ""] \in [a : {1, "a"}, b : STRING]
    OBVIOUS
  <1>2. QED BY <1>1 DEF Cases!ToStringMixed

THEOREM PrintMixed == Cases!PrintMixed
  BY DEF Cases!PrintMixed

THEOREM TLCEvalMixed == Cases!TLCEvalMixed
  BY DEF Cases!TLCEvalMixed
=============================================================================
