---------------------- MODULE ValueSemanticsTheorems ------------------------
\* Representation-independent proofs of the propositions that
\* ValueSemanticsAssume.tla asks TLC to evaluate.
EXTENDS FiniteSets, FiniteSetTheorems, Integers, Sequences, TLAPS

CONSTANT Model

Cases == INSTANCE ValueSemanticsCases
  WITH Cardinality <- Cardinality,
       IsFiniteSet <- IsFiniteSet,
       Fingerprint <- LAMBDA value : value,
       Combine <- LAMBDA f, g :
                    [x \in (DOMAIN f) \cup (DOMAIN g) |->
                       IF x \in DOMAIN f THEN f[x] ELSE g[x]],
       Model <- Model

LEMMA PairFiniteCardinality ==
  ASSUME NEW a, NEW b, a # b
  PROVE  IsFiniteSet({a, b}) /\ Cardinality({a, b}) = 2
  <1>1. IsFiniteSet({b}) /\ Cardinality({b}) = 1
    BY FS_Singleton
  <1>2. a \notin {b}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2, FS_AddElement

LEMMA TripleFiniteCardinality ==
  ASSUME NEW a, NEW b, NEW c, a # b, a # c, b # c
  PROVE  IsFiniteSet({a, b, c}) /\ Cardinality({a, b, c}) = 3
  <1>1. IsFiniteSet({b, c}) /\ Cardinality({b, c}) = 2
    BY PairFiniteCardinality
  <1>2. a \notin {b, c}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2, FS_AddElement

LEMMA QuadFiniteCardinality ==
  ASSUME NEW a, NEW b, NEW c, NEW d,
         a # b, a # c, a # d, b # c, b # d, c # d
  PROVE  IsFiniteSet({a, b, c, d}) /\ Cardinality({a, b, c, d}) = 4
  <1>1. IsFiniteSet({b, c, d}) /\ Cardinality({b, c, d}) = 3
    BY TripleFiniteCardinality
  <1>2. a \notin {b, c, d}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2, FS_AddElement

THEOREM IntReflexive == Cases!IntReflexive
  BY DEF Cases!IntReflexive

THEOREM IntNestedDuplicate == Cases!IntNestedDuplicate
  BY FS_Singleton DEF Cases!IntNestedDuplicate

THEOREM StringReflexive == Cases!StringReflexive
  BY DEF Cases!StringReflexive

THEOREM StringNestedDuplicate == Cases!StringNestedDuplicate
  BY FS_Singleton DEF Cases!StringNestedDuplicate

THEOREM BoolReflexive == Cases!BoolReflexive
  BY DEF Cases!BoolReflexive

THEOREM BoolNestedDuplicate == Cases!BoolNestedDuplicate
  BY FS_Singleton DEF Cases!BoolNestedDuplicate

THEOREM ModelReflexive == Cases!ModelReflexive
  BY DEF Cases!ModelReflexive

THEOREM ModelNestedDuplicate == Cases!ModelNestedDuplicate
  BY FS_Singleton DEF Cases!ModelNestedDuplicate

THEOREM EnumPermutation == Cases!EnumPermutation
  BY DEF Cases!EnumPermutation

THEOREM EnumDuplicates == Cases!EnumDuplicates
  BY DEF Cases!EnumDuplicates

THEOREM EnumMember == Cases!EnumMember
  BY DEF Cases!EnumMember

THEOREM EnumNotMember == Cases!EnumNotMember
  BY DEF Cases!EnumNotMember

THEOREM CardEnum == Cases!CardEnum
  BY TripleFiniteCardinality DEF Cases!CardEnum

THEOREM FiniteEnum == Cases!FiniteEnum
  BY TripleFiniteCardinality DEF Cases!FiniteEnum

THEOREM FPEnumPermutation == Cases!FPEnumPermutation
  BY EnumPermutation DEF Cases!FPEnumPermutation, Cases!EnumPermutation

THEOREM IntervalEqEnum == Cases!IntervalEqEnum
  BY DEF Cases!IntervalEqEnum

THEOREM EnumEqInterval == Cases!EnumEqInterval
  BY IntervalEqEnum DEF Cases!EnumEqInterval, Cases!IntervalEqEnum

THEOREM IntervalNested == Cases!IntervalNested
  BY IntervalEqEnum, FS_Singleton
     DEF Cases!IntervalNested, Cases!IntervalEqEnum

THEOREM IntervalDuplicate == Cases!IntervalDuplicate
  BY FS_Singleton DEF Cases!IntervalDuplicate

THEOREM IntervalMember == Cases!IntervalMember
  BY DEF Cases!IntervalMember

THEOREM IntervalNotMember == Cases!IntervalNotMember
  BY DEF Cases!IntervalNotMember

THEOREM CardInterval == Cases!CardInterval
  BY IntervalEqEnum, TripleFiniteCardinality
     DEF Cases!CardInterval, Cases!IntervalEqEnum

THEOREM FiniteInterval == Cases!FiniteInterval
  BY IntervalEqEnum, TripleFiniteCardinality
     DEF Cases!FiniteInterval, Cases!IntervalEqEnum

THEOREM FPIntervalEnum == Cases!FPIntervalEnum
  BY IntervalEqEnum DEF Cases!FPIntervalEnum, Cases!IntervalEqEnum

THEOREM SubsetEqEnum == Cases!SubsetEqEnum
  BY DEF Cases!SubsetEqEnum

THEOREM EnumEqSubset == Cases!EnumEqSubset
  BY SubsetEqEnum DEF Cases!EnumEqSubset, Cases!SubsetEqEnum

THEOREM SubsetNested == Cases!SubsetNested
  BY SubsetEqEnum, FS_Singleton
     DEF Cases!SubsetNested, Cases!SubsetEqEnum

THEOREM SubsetBaseDuplicate == Cases!SubsetBaseDuplicate
  BY DEF Cases!SubsetBaseDuplicate

THEOREM SubsetBaseDuplicateNested == Cases!SubsetBaseDuplicateNested
  BY SubsetBaseDuplicate, FS_Singleton
     DEF Cases!SubsetBaseDuplicateNested, Cases!SubsetBaseDuplicate

THEOREM SubsetMember == Cases!SubsetMember
  BY DEF Cases!SubsetMember

THEOREM SubsetNotMember == Cases!SubsetNotMember
  BY DEF Cases!SubsetNotMember

THEOREM CardSubset == Cases!CardSubset
  BY SubsetEqEnum, QuadFiniteCardinality
     DEF Cases!CardSubset, Cases!SubsetEqEnum

THEOREM FiniteSubset == Cases!FiniteSubset
  BY SubsetEqEnum, QuadFiniteCardinality
     DEF Cases!FiniteSubset, Cases!SubsetEqEnum

THEOREM FPSubsetEnum == Cases!FPSubsetEnum
  BY SubsetEqEnum DEF Cases!FPSubsetEnum, Cases!SubsetEqEnum

THEOREM CapEqEnum == Cases!CapEqEnum
  BY DEF Cases!CapEqEnum

THEOREM EnumEqCap == Cases!EnumEqCap
  BY CapEqEnum DEF Cases!EnumEqCap, Cases!CapEqEnum

THEOREM CapNested == Cases!CapNested
  BY CapEqEnum, FS_Singleton DEF Cases!CapNested, Cases!CapEqEnum

THEOREM CapSym == Cases!CapSym
  BY DEF Cases!CapSym

THEOREM CapSymNested == Cases!CapSymNested
  BY CapSym, FS_Singleton DEF Cases!CapSymNested, Cases!CapSym

THEOREM CapMember == Cases!CapMember
  BY DEF Cases!CapMember

THEOREM CapNotMember == Cases!CapNotMember
  BY DEF Cases!CapNotMember

THEOREM CardCap == Cases!CardCap
  BY CapEqEnum, PairFiniteCardinality
     DEF Cases!CardCap, Cases!CapEqEnum

THEOREM FiniteCap == Cases!FiniteCap
  BY CapEqEnum, PairFiniteCardinality
     DEF Cases!FiniteCap, Cases!CapEqEnum

THEOREM FPCapEnum == Cases!FPCapEnum
  BY CapEqEnum DEF Cases!FPCapEnum, Cases!CapEqEnum

THEOREM DiffEqEnum == Cases!DiffEqEnum
  BY DEF Cases!DiffEqEnum

THEOREM EnumEqDiff == Cases!EnumEqDiff
  BY DiffEqEnum DEF Cases!EnumEqDiff, Cases!DiffEqEnum

THEOREM DiffNested == Cases!DiffNested
  BY DiffEqEnum, FS_Singleton DEF Cases!DiffNested, Cases!DiffEqEnum

THEOREM DiffSameEmpty == Cases!DiffSameEmpty
  BY DEF Cases!DiffSameEmpty

THEOREM DiffSameNested == Cases!DiffSameNested
  BY DiffSameEmpty, FS_Singleton
     DEF Cases!DiffSameNested, Cases!DiffSameEmpty

THEOREM LazyDiffEqEnum == Cases!LazyDiffEqEnum
  BY DEF Cases!LazyDiffEqEnum, Cases!PredTwo

THEOREM LazyDiffMember == Cases!LazyDiffMember
  BY DEF Cases!LazyDiffMember, Cases!PredTwo

THEOREM LazyDiffNotMember == Cases!LazyDiffNotMember
  BY DEF Cases!LazyDiffNotMember, Cases!PredTwo

THEOREM CardLazyDiff == Cases!CardLazyDiff
  BY LazyDiffEqEnum, FS_Singleton
     DEF Cases!CardLazyDiff, Cases!LazyDiffEqEnum

THEOREM FiniteLazyDiff == Cases!FiniteLazyDiff
  BY LazyDiffEqEnum, FS_Singleton
     DEF Cases!FiniteLazyDiff, Cases!LazyDiffEqEnum

THEOREM FPLazyDiffEnum == Cases!FPLazyDiffEnum
  BY LazyDiffEqEnum
     DEF Cases!FPLazyDiffEnum, Cases!LazyDiffEqEnum

THEOREM CupEqEnum == Cases!CupEqEnum
  BY DEF Cases!CupEqEnum

THEOREM EnumEqCup == Cases!EnumEqCup
  BY CupEqEnum DEF Cases!EnumEqCup, Cases!CupEqEnum

THEOREM CupNested == Cases!CupNested
  BY CupEqEnum, FS_Singleton DEF Cases!CupNested, Cases!CupEqEnum

THEOREM CupSym == Cases!CupSym
  BY DEF Cases!CupSym

THEOREM CupSymNested == Cases!CupSymNested
  BY CupSym, FS_Singleton DEF Cases!CupSymNested, Cases!CupSym

THEOREM LazyCupEqEnum == Cases!LazyCupEqEnum
  BY DEF Cases!LazyCupEqEnum, Cases!PredTwo

THEOREM LazyCupMember == Cases!LazyCupMember
  BY DEF Cases!LazyCupMember, Cases!PredTwo

THEOREM LazyCupNotMember == Cases!LazyCupNotMember
  BY DEF Cases!LazyCupNotMember, Cases!PredTwo

THEOREM CardLazyCup == Cases!CardLazyCup
  BY LazyCupEqEnum, TripleFiniteCardinality
     DEF Cases!CardLazyCup, Cases!LazyCupEqEnum

THEOREM FiniteLazyCup == Cases!FiniteLazyCup
  BY LazyCupEqEnum, TripleFiniteCardinality
     DEF Cases!FiniteLazyCup, Cases!LazyCupEqEnum

THEOREM FPLazyCupEnum == Cases!FPLazyCupEnum
  BY LazyCupEqEnum
     DEF Cases!FPLazyCupEnum, Cases!LazyCupEqEnum

THEOREM UnionPower == Cases!UnionPower
  BY DEF Cases!UnionPower

THEOREM UnionPowerRev == Cases!UnionPowerRev
  BY UnionPower DEF Cases!UnionPowerRev, Cases!UnionPower

THEOREM UnionPowerNested == Cases!UnionPowerNested
  BY UnionPower, FS_Singleton
     DEF Cases!UnionPowerNested, Cases!UnionPower

THEOREM UnionDuplicate == Cases!UnionDuplicate
  BY DEF Cases!UnionDuplicate

THEOREM UnionMember == Cases!UnionMember
  BY DEF Cases!UnionMember

THEOREM UnionNotMember == Cases!UnionNotMember
  BY DEF Cases!UnionNotMember

THEOREM CardUnion == Cases!CardUnion
  BY UnionPower, PairFiniteCardinality
     DEF Cases!CardUnion, Cases!UnionPower

THEOREM FiniteUnion == Cases!FiniteUnion
  BY UnionPower, PairFiniteCardinality
     DEF Cases!FiniteUnion, Cases!UnionPower

THEOREM FPUnionEnum == Cases!FPUnionEnum
  BY UnionPower DEF Cases!FPUnionEnum, Cases!UnionPower

THEOREM PredEqEnum == Cases!PredEqEnum
  BY SMT DEF Cases!PredEqEnum

THEOREM EnumEqPred == Cases!EnumEqPred
  BY PredEqEnum DEF Cases!EnumEqPred, Cases!PredEqEnum

THEOREM PredNested == Cases!PredNested
  BY PredEqEnum, FS_Singleton DEF Cases!PredNested, Cases!PredEqEnum

THEOREM PredAll == Cases!PredAll
  BY DEF Cases!PredAll

THEOREM PredAllNested == Cases!PredAllNested
  BY PredAll, FS_Singleton DEF Cases!PredAllNested, Cases!PredAll

THEOREM PredMember == Cases!PredMember
  BY SMT DEF Cases!PredMember

THEOREM PredNotMember == Cases!PredNotMember
  BY SMT DEF Cases!PredNotMember

THEOREM CardPred == Cases!CardPred
  BY PredEqEnum, PairFiniteCardinality
     DEF Cases!CardPred, Cases!PredEqEnum

THEOREM FinitePred == Cases!FinitePred
  BY PredEqEnum, PairFiniteCardinality
     DEF Cases!FinitePred, Cases!PredEqEnum

THEOREM FPPredEnum == Cases!FPPredEnum
  BY PredEqEnum DEF Cases!FPPredEnum, Cases!PredEqEnum

THEOREM FcnEqRecord == Cases!FcnEqRecord
  BY DEF Cases!FcnEqRecord, Cases!F, Cases!R

THEOREM RecordEqFcn == Cases!RecordEqFcn
  BY FcnEqRecord DEF Cases!RecordEqFcn, Cases!FcnEqRecord

THEOREM FcnRecordNested == Cases!FcnRecordNested
  BY FcnEqRecord, FS_Singleton
     DEF Cases!FcnRecordNested, Cases!FcnEqRecord

THEOREM FcnEqTuple == Cases!FcnEqTuple
  BY DEF Cases!FcnEqTuple, Cases!T

THEOREM TupleEqFcn == Cases!TupleEqFcn
  BY FcnEqTuple DEF Cases!TupleEqFcn, Cases!FcnEqTuple

THEOREM FcnTupleNested == Cases!FcnTupleNested
  BY FcnEqTuple, FS_Singleton
     DEF Cases!FcnTupleNested, Cases!FcnEqTuple

THEOREM RecordEqTupleFunction == Cases!RecordEqTupleFunction
  BY DEF Cases!RecordEqTupleFunction

THEOREM FcnDomain == Cases!FcnDomain
  BY DEF Cases!FcnDomain, Cases!F

THEOREM FcnApply == Cases!FcnApply
  BY DEF Cases!FcnApply, Cases!F

THEOREM RecordDomain == Cases!RecordDomain
  BY DEF Cases!RecordDomain, Cases!R

THEOREM RecordApply == Cases!RecordApply
  BY DEF Cases!RecordApply, Cases!R

THEOREM TupleDomain == Cases!TupleDomain
  BY DEF Cases!TupleDomain, Cases!T

THEOREM TupleApply == Cases!TupleApply
  BY DEF Cases!TupleApply, Cases!T

THEOREM FPFcnRecord == Cases!FPFcnRecord
  BY FcnEqRecord DEF Cases!FPFcnRecord, Cases!FcnEqRecord

THEOREM FPFcnTuple == Cases!FPFcnTuple
  BY FcnEqTuple DEF Cases!FPFcnTuple, Cases!FcnEqTuple

THEOREM LazySetEquality == Cases!LazySetEquality
  BY DEF Cases!LazySetEquality

THEOREM LazySetNested == Cases!LazySetNested
  BY FS_Singleton DEF Cases!LazySetNested

THEOREM LazyFcnApplication == Cases!LazyFcnApplication
  BY DEF Cases!LazyFcnApplication

THEOREM FcnExceptSame == Cases!FcnExceptSame
  BY DEF Cases!FcnExceptSame, Cases!F

THEOREM FcnExceptUpdate == Cases!FcnExceptUpdate
  BY DEF Cases!FcnExceptUpdate, Cases!F

THEOREM TupleExceptSame == Cases!TupleExceptSame
  BY DEF Cases!TupleExceptSame, Cases!T

THEOREM TupleExceptUpdate == Cases!TupleExceptUpdate
  BY DEF Cases!TupleExceptUpdate, Cases!T

THEOREM RecordExceptSame == Cases!RecordExceptSame
  BY DEF Cases!RecordExceptSame, Cases!R

THEOREM RecordExceptUpdate == Cases!RecordExceptUpdate
  BY DEF Cases!RecordExceptUpdate, Cases!R

THEOREM FPFcnExceptSame == Cases!FPFcnExceptSame
  BY FcnExceptSame
     DEF Cases!FPFcnExceptSame, Cases!FcnExceptSame

THEOREM FPTupleExceptSame == Cases!FPTupleExceptSame
  BY TupleExceptSame
     DEF Cases!FPTupleExceptSame, Cases!TupleExceptSame

THEOREM FPRecordExceptSame == Cases!FPRecordExceptSame
  BY RecordExceptSame
     DEF Cases!FPRecordExceptSame, Cases!RecordExceptSame

THEOREM FcnExceptMissing == Cases!FcnExceptMissing
  BY DEF Cases!FcnExceptMissing, Cases!F

THEOREM TupleExceptMissing == Cases!TupleExceptMissing
  BY DEF Cases!TupleExceptMissing, Cases!T

THEOREM RecordExceptMissing == Cases!RecordExceptMissing
  BY DEF Cases!RecordExceptMissing, Cases!R

THEOREM NestedFcnExcept == Cases!NestedFcnExcept
  BY DEF Cases!NestedFcnExcept, Cases!NestedFcn

THEOREM NestedTupleExcept == Cases!NestedTupleExcept
  BY DEF Cases!NestedTupleExcept

THEOREM NestedRecordExcept == Cases!NestedRecordExcept
  BY DEF Cases!NestedRecordExcept

THEOREM FcnExceptAt == Cases!FcnExceptAt
  BY DEF Cases!FcnExceptAt, Cases!F

THEOREM TupleExceptAt == Cases!TupleExceptAt
  BY DEF Cases!TupleExceptAt, Cases!T

THEOREM RecordExceptAt == Cases!RecordExceptAt
  BY DEF Cases!RecordExceptAt, Cases!R

THEOREM NestedExceptMissing == Cases!NestedExceptMissing
  BY DEF Cases!NestedExceptMissing, Cases!NestedFcn

THEOREM FcnExceptLastWins == Cases!FcnExceptLastWins
  BY DEF Cases!FcnExceptLastWins, Cases!F

THEOREM FcnExceptAtNested == Cases!FcnExceptAtNested
  BY DEF Cases!FcnExceptAtNested, Cases!F

THEOREM TupleExceptLastWins == Cases!TupleExceptLastWins
  BY DEF Cases!TupleExceptLastWins, Cases!T

THEOREM FcnCombineDisjoint == Cases!FcnCombineDisjoint
  BY DEF Cases!FcnCombineDisjoint

THEOREM FcnCombineLeftWins == Cases!FcnCombineLeftWins
  BY DEF Cases!FcnCombineLeftWins

THEOREM IntervalFcnCombine == Cases!IntervalFcnCombine
  <1>1. 1..1 = {1}
    OBVIOUS
  <1>2. QED BY <1>1 DEF Cases!IntervalFcnCombine

THEOREM IntervalEmptySubsetEmpty == Cases!IntervalEmptySubsetEmpty
  BY DEF Cases!IntervalEmptySubsetEmpty

THEOREM IntervalEmptySubsetEnum == Cases!IntervalEmptySubsetEnum
  BY DEF Cases!IntervalEmptySubsetEnum

THEOREM IntervalEmptySubsetNat == Cases!IntervalEmptySubsetNat
  BY DEF Cases!IntervalEmptySubsetNat

THEOREM IntervalNotSubsetEmpty == Cases!IntervalNotSubsetEmpty
  BY DEF Cases!IntervalNotSubsetEmpty

THEOREM EmptyIntervalsNested == Cases!EmptyIntervalsNested
  <1>1. 2..1 = {}
    OBVIOUS
  <1>2. 5..4 = {}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2, FS_Singleton DEF Cases!EmptyIntervalsNested

THEOREM FPEmptyIntervals == Cases!FPEmptyIntervals
  BY DEF Cases!FPEmptyIntervals

THEOREM EmptyIntervalFcnEqTuple == Cases!EmptyIntervalFcnEqTuple
  <1>1. 2..1 = {}
    OBVIOUS
  <1>2. [x \in {} |-> x] = <<>>
    OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF Cases!EmptyIntervalFcnEqTuple

THEOREM EmptyEnumFcnEqTuple == Cases!EmptyEnumFcnEqTuple
  BY DEF Cases!EmptyEnumFcnEqTuple

THEOREM EmptyTupleEqIntervalFcn == Cases!EmptyTupleEqIntervalFcn
  BY EmptyIntervalFcnEqTuple
     DEF Cases!EmptyTupleEqIntervalFcn, Cases!EmptyIntervalFcnEqTuple

THEOREM EmptyIntervalFcnsEq == Cases!EmptyIntervalFcnsEq
  <1>1. 2..1 = {}
    OBVIOUS
  <1>2. 3..2 = {}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF Cases!EmptyIntervalFcnsEq

LEMMA TwoEmptyIntervalFcnsSingleton ==
  {[x \in 2..1 |-> x], [x \in 3..2 |-> x]}
    = {[x \in 2..1 |-> x]}
  <1>1. [x \in 2..1 |-> x] = [x \in 3..2 |-> x]
    BY EmptyIntervalFcnsEq DEF Cases!EmptyIntervalFcnsEq
  <1>2. QED BY <1>1

THEOREM EmptyIntervalFcnsNested == Cases!EmptyIntervalFcnsNested
  BY TwoEmptyIntervalFcnsSingleton, FS_Singleton
     DEF Cases!EmptyIntervalFcnsNested

THEOREM EmptyIntervalFcnsSetEq == Cases!EmptyIntervalFcnsSetEq
  BY TwoEmptyIntervalFcnsSingleton DEF Cases!EmptyIntervalFcnsSetEq

THEOREM NegativeEmptyIntervalFcnEqTuple ==
  Cases!NegativeEmptyIntervalFcnEqTuple
  <1>1. 1..(-1) = {}
    OBVIOUS
  <1>2. [x \in {} |-> x] = <<>>
    OBVIOUS
  <1>3. QED BY <1>1, <1>2
    DEF Cases!NegativeEmptyIntervalFcnEqTuple

THEOREM EmptyTupleEqNegativeIntervalFcn ==
  Cases!EmptyTupleEqNegativeIntervalFcn(0)
  BY NegativeEmptyIntervalFcnEqTuple
     DEF Cases!EmptyTupleEqNegativeIntervalFcn,
         Cases!NegativeEmptyIntervalFcnEqTuple

LEMMA MixedEmptyFcnSingleton ==
  {[x \in 2..1 |-> x], <<>>} = {<<>>}
  <1>1. [x \in 2..1 |-> x] = <<>>
    BY EmptyIntervalFcnEqTuple
  <1>2. QED BY <1>1

THEOREM EmptyIntervalFcnNested == Cases!EmptyIntervalFcnNested
  BY MixedEmptyFcnSingleton, FS_Singleton
     DEF Cases!EmptyIntervalFcnNested

THEOREM EmptyEnumFcnNested == Cases!EmptyEnumFcnNested
  <1>1. {[x \in {} |-> x], <<>>} = {<<>>}
    BY EmptyEnumFcnEqTuple
  <1>2. QED BY <1>1, FS_Singleton DEF Cases!EmptyEnumFcnNested

THEOREM EmptyFcnDomainsNested == Cases!EmptyFcnDomainsNested
  BY EmptyIntervalFcnEqTuple, EmptyEnumFcnEqTuple, FS_Singleton
     DEF Cases!EmptyFcnDomainsNested, Cases!EmptyIntervalFcnEqTuple,
         Cases!EmptyEnumFcnEqTuple

THEOREM EmptyFcnNested == Cases!EmptyFcnNested
  BY EmptyIntervalFcnEqTuple, EmptyEnumFcnEqTuple, FS_Singleton
     DEF Cases!EmptyFcnNested, Cases!EmptyIntervalFcnEqTuple,
         Cases!EmptyEnumFcnEqTuple

THEOREM EmptyFcnSetEqSingleton == Cases!EmptyFcnSetEqSingleton
  BY EmptyIntervalFcnEqTuple, EmptyEnumFcnEqTuple
     DEF Cases!EmptyFcnSetEqSingleton, Cases!EmptyIntervalFcnEqTuple,
         Cases!EmptyEnumFcnEqTuple

THEOREM EmptyFcnSetPermutation == Cases!EmptyFcnSetPermutation
  BY DEF Cases!EmptyFcnSetPermutation

THEOREM ChooseEmptyFcnSet == Cases!ChooseEmptyFcnSet
  BY EmptyFcnSetEqSingleton
     DEF Cases!ChooseEmptyFcnSet, Cases!EmptyFcnSetEqSingleton

THEOREM FPEmptyFcnTuple == Cases!FPEmptyFcnTuple
  BY EmptyIntervalFcnEqTuple
     DEF Cases!FPEmptyFcnTuple, Cases!EmptyIntervalFcnEqTuple

THEOREM FPMixedEmptyFcnSet == Cases!FPMixedEmptyFcnSet
  BY EmptyIntervalFcnEqTuple
     DEF Cases!FPMixedEmptyFcnSet, Cases!EmptyIntervalFcnEqTuple

THEOREM CardSubsetMixedEmptyFcn == Cases!CardSubsetMixedEmptyFcn
  <1>1. SUBSET {[x \in 2..1 |-> x], <<>>} = {{}, {<<>>}}
    BY MixedEmptyFcnSingleton
  <1>2. {} # {<<>>}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2, PairFiniteCardinality
    DEF Cases!CardSubsetMixedEmptyFcn

THEOREM SubsetMixedEmptyFcnEq == Cases!SubsetMixedEmptyFcnEq
  BY MixedEmptyFcnSingleton DEF Cases!SubsetMixedEmptyFcnEq

THEOREM CardCupMixedEmptyFcn == Cases!CardCupMixedEmptyFcn
  BY EmptyIntervalFcnEqTuple, FS_Singleton
     DEF Cases!CardCupMixedEmptyFcn, Cases!EmptyIntervalFcnEqTuple

THEOREM CardUnionMixedEmptyFcn == Cases!CardUnionMixedEmptyFcn
  <1>1. UNION {{[x \in 2..1 |-> x]}, {<<>>}} = {<<>>}
    BY MixedEmptyFcnSingleton
  <1>2. QED BY <1>1, FS_Singleton DEF Cases!CardUnionMixedEmptyFcn

THEOREM CardFcnSetMixedEmptyFcn == Cases!CardFcnSetMixedEmptyFcn
  <1>1. [{[x \in 2..1 |-> x], <<>>} -> {0, 1}]
      = {[x \in {<<>>} |-> 0], [x \in {<<>>} |-> 1]}
    BY MixedEmptyFcnSingleton
  <1>2. [x \in {<<>>} |-> 0] # [x \in {<<>>} |-> 1]
    OBVIOUS
  <1>3. QED BY <1>1, <1>2, PairFiniteCardinality
    DEF Cases!CardFcnSetMixedEmptyFcn

THEOREM CardRcdSetMixedEmptyFcn == Cases!CardRcdSetMixedEmptyFcn
  <1>1. [a : {[x \in 2..1 |-> x], <<>>}] = {[a |-> <<>>]}
    BY MixedEmptyFcnSingleton
  <1>2. QED BY <1>1, FS_Singleton
    DEF Cases!CardRcdSetMixedEmptyFcn

THEOREM CardTupleSetMixedEmptyFcn == Cases!CardTupleSetMixedEmptyFcn
  <1>1. {[x \in 2..1 |-> x], <<>>} \X {0} = {<<<<>>, 0>>}
    BY MixedEmptyFcnSingleton
  <1>2. QED BY <1>1, FS_Singleton
    DEF Cases!CardTupleSetMixedEmptyFcn

THEOREM EmptyIntervalBodiesEq == Cases!EmptyIntervalBodiesEq
  <1>1. 2..1 = {}
    OBVIOUS
  <1>2. 5..4 = {}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF Cases!EmptyIntervalBodiesEq

THEOREM EmptyZeroIntervalFcnEqTuple == Cases!EmptyZeroIntervalFcnEqTuple
  <1>1. 0..(-1) = {}
    OBVIOUS
  <1>2. [x \in {} |-> x] = <<>>
    OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF Cases!EmptyZeroIntervalFcnEqTuple

THEOREM EmptyCanonicalVsOtherInterval ==
  Cases!EmptyCanonicalVsOtherInterval
  <1>1. 1..0 = {}
    OBVIOUS
  <1>2. 2..1 = {}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF Cases!EmptyCanonicalVsOtherInterval

THEOREM EmptyIntervalBodiesNested == Cases!EmptyIntervalBodiesNested
  <1>1. {[x \in 2..1 |-> 1], [x \in 5..4 |-> 99]}
      = {[x \in 2..1 |-> 1]}
    BY EmptyIntervalBodiesEq
  <1>2. QED BY <1>1, FS_Singleton DEF Cases!EmptyIntervalBodiesNested

THEOREM EmptyCanonicalVsOtherNested == Cases!EmptyCanonicalVsOtherNested
  <1>1. {[x \in 1..0 |-> x], [x \in 2..1 |-> x]}
      = {[x \in 1..0 |-> x]}
    BY EmptyCanonicalVsOtherInterval
  <1>2. QED BY <1>1, FS_Singleton DEF Cases!EmptyCanonicalVsOtherNested

THEOREM EmptyFcnSingletonEq == Cases!EmptyFcnSingletonEq
  BY EmptyIntervalFcnEqTuple DEF Cases!EmptyFcnSingletonEq,
                                 Cases!EmptyIntervalFcnEqTuple

THEOREM EmptyFcnDomainEq == Cases!EmptyFcnDomainEq
  BY EmptyIntervalFcnEqTuple DEF Cases!EmptyFcnDomainEq,
                                 Cases!EmptyIntervalFcnEqTuple

THEOREM EmptyFcnExceptNoop == Cases!EmptyFcnExceptNoop
  BY EmptyIntervalFcnEqTuple DEF Cases!EmptyFcnExceptNoop,
                                 Cases!EmptyIntervalFcnEqTuple

THEOREM NestedEmptyFcnEq == Cases!NestedEmptyFcnEq
  BY EmptyIntervalFcnEqTuple DEF Cases!NestedEmptyFcnEq,
                                 Cases!EmptyIntervalFcnEqTuple

THEOREM NestedEmptyFcnNested == Cases!NestedEmptyFcnNested
  <1>1. {[i \in {1} |-> [x \in 2..1 |-> x]], [i \in {1} |-> <<>>]}
      = {[i \in {1} |-> <<>>]}
    BY NestedEmptyFcnEq, EmptyIntervalFcnEqTuple
       DEF Cases!NestedEmptyFcnEq, Cases!EmptyIntervalFcnEqTuple
  <1>2. QED BY <1>1, FS_Singleton DEF Cases!NestedEmptyFcnNested

THEOREM NestedEmptyRecordEq == Cases!NestedEmptyRecordEq
  BY EmptyIntervalFcnEqTuple DEF Cases!NestedEmptyRecordEq,
                                 Cases!EmptyIntervalFcnEqTuple

THEOREM NestedEmptyRecordNested == Cases!NestedEmptyRecordNested
  <1>1. [x \in 2..1 |-> x] = <<>>
    BY EmptyIntervalFcnEqTuple
  <1>2. [a |-> [x \in 2..1 |-> x]] = [a |-> <<>>]
    BY <1>1
  <1>3. {[a |-> [x \in 2..1 |-> x]], [a |-> <<>>]} = {[a |-> <<>>]}
    BY <1>2
  <1>4. QED BY <1>3, FS_Singleton DEF Cases!NestedEmptyRecordNested

THEOREM NestedEmptyTupleEq == Cases!NestedEmptyTupleEq
  BY EmptyIntervalFcnEqTuple DEF Cases!NestedEmptyTupleEq,
                                 Cases!EmptyIntervalFcnEqTuple

THEOREM NestedEmptyTupleNested == Cases!NestedEmptyTupleNested
  <1>1. [x \in 2..1 |-> x] = <<>>
    BY EmptyIntervalFcnEqTuple
  <1>2. <<[x \in 2..1 |-> x]>> = <<<<>>>>
    BY <1>1
  <1>3. {<<[x \in 2..1 |-> x]>>, <<<<>>>>} = {<<<<>>>>}
    BY <1>2
  <1>4. QED BY <1>3, FS_Singleton DEF Cases!NestedEmptyTupleNested

THEOREM FPEmptyIntervalFcns == Cases!FPEmptyIntervalFcns
  BY EmptyIntervalFcnsEq DEF Cases!FPEmptyIntervalFcns,
                             Cases!EmptyIntervalFcnsEq

THEOREM FcnSetEqEnum == Cases!FcnSetEqEnum
  BY DEF Cases!FcnSetEqEnum

THEOREM FcnSetEqEnumRev == Cases!FcnSetEqEnumRev
  BY FcnSetEqEnum DEF Cases!FcnSetEqEnumRev, Cases!FcnSetEqEnum

THEOREM FcnSetNested == Cases!FcnSetNested
  BY FcnSetEqEnum, FS_Singleton
     DEF Cases!FcnSetNested, Cases!FcnSetEqEnum

THEOREM FcnSetMember == Cases!FcnSetMember
  BY DEF Cases!FcnSetMember

THEOREM FcnSetNotMember == Cases!FcnSetNotMember
  BY DEF Cases!FcnSetNotMember

THEOREM CardFcnSet == Cases!CardFcnSet
  BY FcnSetEqEnum, PairFiniteCardinality
     DEF Cases!CardFcnSet, Cases!FcnSetEqEnum

THEOREM FiniteFcnSet == Cases!FiniteFcnSet
  BY FcnSetEqEnum, PairFiniteCardinality
     DEF Cases!FiniteFcnSet, Cases!FcnSetEqEnum

THEOREM FPFcnSetEnum == Cases!FPFcnSetEnum
  BY FcnSetEqEnum DEF Cases!FPFcnSetEnum, Cases!FcnSetEqEnum

THEOREM EmptyDomainFcnSetEq == Cases!EmptyDomainFcnSetEq
  BY DEF Cases!EmptyDomainFcnSetEq

THEOREM EmptyDomainFcnSetSingleton == Cases!EmptyDomainFcnSetSingleton
  BY DEF Cases!EmptyDomainFcnSetSingleton

THEOREM EmptyIntervalDomainFcnSetEq ==
  Cases!EmptyIntervalDomainFcnSetEq
  <1>1. 2..1 = {}
    OBVIOUS
  <1>2. QED BY <1>1 DEF Cases!EmptyIntervalDomainFcnSetEq

THEOREM CardSingletonRangeNat == Cases!CardSingletonRangeNat
  <1>1. [Nat -> {0}] = {[x \in Nat |-> 0]}
    OBVIOUS
  <1>2. QED BY <1>1, FS_Singleton DEF Cases!CardSingletonRangeNat

THEOREM FiniteSingletonRangeNat == Cases!FiniteSingletonRangeNat
  <1>1. [Nat -> {0}] = {[x \in Nat |-> 0]}
    OBVIOUS
  <1>2. QED BY <1>1, FS_Singleton DEF Cases!FiniteSingletonRangeNat

THEOREM EmptyFcnInEmptyDomainSet == Cases!EmptyFcnInEmptyDomainSet
  BY EmptyIntervalFcnEqTuple DEF Cases!EmptyFcnInEmptyDomainSet,
                                 Cases!EmptyIntervalFcnEqTuple

THEOREM EmptyRangeNatEqEmpty == Cases!EmptyRangeNatEqEmpty
  <1> SUFFICES ASSUME NEW f \in [Nat -> {}]
               PROVE  FALSE
    BY DEF Cases!EmptyRangeNatEqEmpty
  <1>1. 0 \in Nat
    OBVIOUS
  <1>2. f[0] \in {}
    BY <1>1
  <1>3. QED BY <1>2

THEOREM CardEmptyRangeNat == Cases!CardEmptyRangeNat
  BY EmptyRangeNatEqEmpty, FS_EmptySet
     DEF Cases!CardEmptyRangeNat, Cases!EmptyRangeNatEqEmpty

THEOREM FiniteEmptyRangeNat == Cases!FiniteEmptyRangeNat
  BY EmptyRangeNatEqEmpty, FS_EmptySet
     DEF Cases!FiniteEmptyRangeNat, Cases!EmptyRangeNatEqEmpty

THEOREM EmptyRangeFcnSetSingleton == Cases!EmptyRangeFcnSetSingleton
  BY DEF Cases!EmptyRangeFcnSetSingleton

THEOREM EmptyFcnInEmptyRangeSet == Cases!EmptyFcnInEmptyRangeSet
  BY EmptyRangeFcnSetSingleton
     DEF Cases!EmptyFcnInEmptyRangeSet, Cases!EmptyRangeFcnSetSingleton

THEOREM NatZeroFcnApply == Cases!NatZeroFcnApply
  BY DEF Cases!NatZeroFcnApply

THEOREM NatExceptApply == Cases!NatExceptApply
  BY DEF Cases!NatExceptApply

THEOREM NatExceptOrig == Cases!NatExceptOrig
  BY DEF Cases!NatExceptOrig

THEOREM NatExceptAt == Cases!NatExceptAt
  BY DEF Cases!NatExceptAt

THEOREM NatExceptDomain == Cases!NatExceptDomain
  BY DEF Cases!NatExceptDomain

THEOREM NatZeroFcnDomain == Cases!NatZeroFcnDomain
  BY DEF Cases!NatZeroFcnDomain

THEOREM StringZeroApply == Cases!StringZeroApply
  BY DEF Cases!StringZeroApply

THEOREM FcnSetNatCupEmpty == Cases!FcnSetNatCupEmpty
  BY DEF Cases!FcnSetNatCupEmpty

THEOREM FcnSetRangeCupEmpty == Cases!FcnSetRangeCupEmpty
  BY DEF Cases!FcnSetRangeCupEmpty

THEOREM EmptyRangeSTRING == Cases!EmptyRangeSTRING
  <1> SUFFICES ASSUME NEW f \in [STRING -> {}]
               PROVE  FALSE
    BY DEF Cases!EmptyRangeSTRING
  <1>1. "" \in STRING
    OBVIOUS
  <1>2. f[""] \in {}
    BY <1>1
  <1>3. QED BY <1>2

THEOREM CardEmptyRangeSTRING == Cases!CardEmptyRangeSTRING
  BY EmptyRangeSTRING, FS_EmptySet
     DEF Cases!CardEmptyRangeSTRING, Cases!EmptyRangeSTRING

THEOREM FiniteEmptyRangeSTRING == Cases!FiniteEmptyRangeSTRING
  BY EmptyRangeSTRING, FS_EmptySet
     DEF Cases!FiniteEmptyRangeSTRING, Cases!EmptyRangeSTRING

THEOREM RcdSetEqEnum == Cases!RcdSetEqEnum
  BY DEF Cases!RcdSetEqEnum

THEOREM RcdSetEqEnumRev == Cases!RcdSetEqEnumRev
  BY RcdSetEqEnum DEF Cases!RcdSetEqEnumRev, Cases!RcdSetEqEnum

THEOREM RcdSetNested == Cases!RcdSetNested
  BY RcdSetEqEnum, FS_Singleton
     DEF Cases!RcdSetNested, Cases!RcdSetEqEnum

THEOREM RcdSetMember == Cases!RcdSetMember
  BY DEF Cases!RcdSetMember

THEOREM RcdSetNotMember == Cases!RcdSetNotMember
  BY DEF Cases!RcdSetNotMember

THEOREM CardRcdSet == Cases!CardRcdSet
  BY RcdSetEqEnum, PairFiniteCardinality
     DEF Cases!CardRcdSet, Cases!RcdSetEqEnum

THEOREM FiniteRcdSet == Cases!FiniteRcdSet
  BY RcdSetEqEnum, PairFiniteCardinality
     DEF Cases!FiniteRcdSet, Cases!RcdSetEqEnum

THEOREM FPRcdSetEnum == Cases!FPRcdSetEnum
  BY RcdSetEqEnum DEF Cases!FPRcdSetEnum, Cases!RcdSetEqEnum

THEOREM EmptyRcdFieldEqEmpty == Cases!EmptyRcdFieldEqEmpty
  <1> SUFFICES ASSUME NEW r \in [a : {}]
               PROVE  FALSE
    BY DEF Cases!EmptyRcdFieldEqEmpty
  <1>1. r.a \in {}
    OBVIOUS
  <1>2. QED BY <1>1

THEOREM EmptyRcdFieldNatEqEmpty == Cases!EmptyRcdFieldNatEqEmpty
  <1> SUFFICES ASSUME NEW r \in [a : Nat, b : {}]
               PROVE  FALSE
    BY DEF Cases!EmptyRcdFieldNatEqEmpty
  <1>1. r.b \in {}
    OBVIOUS
  <1>2. QED BY <1>1

THEOREM FiniteEmptyRcdFieldNat == Cases!FiniteEmptyRcdFieldNat
  BY EmptyRcdFieldNatEqEmpty, FS_EmptySet
     DEF Cases!FiniteEmptyRcdFieldNat, Cases!EmptyRcdFieldNatEqEmpty

THEOREM RcdSetNatCupEmpty == Cases!RcdSetNatCupEmpty
  BY DEF Cases!RcdSetNatCupEmpty

THEOREM RcdNatMember == Cases!RcdNatMember
  BY DEF Cases!RcdNatMember

THEOREM RcdSetBoolEq == Cases!RcdSetBoolEq
  BY DEF Cases!RcdSetBoolEq, Cases!BoolEqEnum

THEOREM RcdSetBoolMember == Cases!RcdSetBoolMember
  BY RcdSetBoolEq DEF Cases!RcdSetBoolMember, Cases!RcdSetBoolEq

THEOREM CardRcdSetBool == Cases!CardRcdSetBool
  BY RcdSetBoolEq, PairFiniteCardinality
     DEF Cases!CardRcdSetBool, Cases!RcdSetBoolEq

THEOREM FiniteRcdSetBool == Cases!FiniteRcdSetBool
  BY RcdSetBoolEq, PairFiniteCardinality
     DEF Cases!FiniteRcdSetBool, Cases!RcdSetBoolEq

THEOREM RcdSetBoolFieldEq == Cases!RcdSetBoolFieldEq
  BY DEF Cases!RcdSetBoolFieldEq, Cases!BoolEqEnum

THEOREM TupleSetEqEnum == Cases!TupleSetEqEnum
  BY DEF Cases!TupleSetEqEnum

THEOREM TupleSetEqEnumRev == Cases!TupleSetEqEnumRev
  BY TupleSetEqEnum DEF Cases!TupleSetEqEnumRev, Cases!TupleSetEqEnum

THEOREM TupleSetNested == Cases!TupleSetNested
  BY TupleSetEqEnum, FS_Singleton
     DEF Cases!TupleSetNested, Cases!TupleSetEqEnum

THEOREM TupleSetMember == Cases!TupleSetMember
  BY DEF Cases!TupleSetMember

THEOREM TupleSetNotMember == Cases!TupleSetNotMember
  BY DEF Cases!TupleSetNotMember

THEOREM CardTupleSet == Cases!CardTupleSet
  BY TupleSetEqEnum, PairFiniteCardinality
     DEF Cases!CardTupleSet, Cases!TupleSetEqEnum

THEOREM FiniteTupleSet == Cases!FiniteTupleSet
  BY TupleSetEqEnum, PairFiniteCardinality
     DEF Cases!FiniteTupleSet, Cases!TupleSetEqEnum

THEOREM FPTupleSetEnum == Cases!FPTupleSetEnum
  BY TupleSetEqEnum DEF Cases!FPTupleSetEnum, Cases!TupleSetEqEnum

THEOREM TupleSetEqFcnSet == Cases!TupleSetEqFcnSet
  <1>1. {1, 2} \X {1, 2} = {<<1, 1>>, <<1, 2>>, <<2, 1>>, <<2, 2>>}
    OBVIOUS
  <1>2. [1..2 -> {1, 2}] = {<<1, 1>>, <<1, 2>>, <<2, 1>>, <<2, 2>>}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF Cases!TupleSetEqFcnSet

THEOREM EmptyProductEq == Cases!EmptyProductEq
  BY DEF Cases!EmptyProductEq

THEOREM EmptyProductEmpty == Cases!EmptyProductEmpty
  BY DEF Cases!EmptyProductEmpty

THEOREM FiniteEmptyProduct == Cases!FiniteEmptyProduct
  BY EmptyProductEmpty, FS_EmptySet
     DEF Cases!FiniteEmptyProduct, Cases!EmptyProductEmpty

THEOREM CardEmptyProduct == Cases!CardEmptyProduct
  BY EmptyProductEmpty, FS_EmptySet
     DEF Cases!CardEmptyProduct, Cases!EmptyProductEmpty

THEOREM EmptyProductIn == Cases!EmptyProductIn
  BY EmptyProductEmpty DEF Cases!EmptyProductIn, Cases!EmptyProductEmpty

THEOREM NestedProductNeqNary == Cases!NestedProductNeqNary
  <1>1. <<1, 2, 3>> \in ({1} \X {2} \X {3})
    OBVIOUS
  <1>2. <<1, 2, 3>> \notin (({1} \X {2}) \X {3})
    OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF Cases!NestedProductNeqNary

THEOREM NaryProductMember == Cases!NaryProductMember
  BY DEF Cases!NaryProductMember

THEOREM NestedProductNotInNary == Cases!NestedProductNotInNary
  BY DEF Cases!NestedProductNotInNary

THEOREM NaryProductEqEnum == Cases!NaryProductEqEnum
  BY DEF Cases!NaryProductEqEnum

THEOREM TupleInSeq == Cases!TupleInSeq
  BY DEF Cases!TupleInSeq

THEOREM FcnInSeq == Cases!FcnInSeq
  BY DEF Cases!FcnInSeq

THEOREM IntCapEnum == Cases!IntCapEnum
  BY DEF Cases!IntCapEnum

THEOREM StringCapEnum == Cases!StringCapEnum
  BY DEF Cases!StringCapEnum

THEOREM SeqCapEnum == Cases!SeqCapEnum
  BY DEF Cases!SeqCapEnum

THEOREM FPIntCapEnum == Cases!FPIntCapEnum
  BY IntCapEnum DEF Cases!FPIntCapEnum, Cases!IntCapEnum

THEOREM FPStringCapEnum == Cases!FPStringCapEnum
  BY StringCapEnum DEF Cases!FPStringCapEnum, Cases!StringCapEnum

THEOREM FPSeqCapEnum == Cases!FPSeqCapEnum
  BY SeqCapEnum DEF Cases!FPSeqCapEnum, Cases!SeqCapEnum

THEOREM EmptySeqInSeqEmpty == Cases!EmptySeqInSeqEmpty
  <1>1. <<>> \in [1..0 -> {}]
    OBVIOUS
  <1>2. 0 \in Nat
    OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF Cases!EmptySeqInSeqEmpty

THEOREM SeqEmptyEq == Cases!SeqEmptyEq(0)
  <1>1. <<>> \in Seq({})
    BY EmptySeqInSeqEmpty DEF Cases!EmptySeqInSeqEmpty
  <1>2. \A s \in Seq({}) : s = <<>>
    <2> SUFFICES ASSUME NEW s \in Seq({})
                 PROVE  s = <<>>
      OBVIOUS
    <2>1. s \in [1..0 -> {}]
      BY <1>1
    <2>2. QED BY <2>1
  <1>3. QED BY <1>1, <1>2 DEF Cases!SeqEmptyEq

THEOREM EmptyInSeqCap == Cases!EmptyInSeqCap
  <1>1. <<>> \in Seq({})
    BY EmptySeqInSeqEmpty DEF Cases!EmptySeqInSeqEmpty
  <1>2. <<>> \in Seq({1})
    <2>1. <<>> \in [1..0 -> {1}]
      OBVIOUS
    <2>2. 0 \in Nat
      OBVIOUS
    <2>3. QED BY <2>1, <2>2
  <1>3. QED BY <1>1, <1>2 DEF Cases!EmptyInSeqCap

THEOREM SeqCapEmptyOneEq == Cases!SeqCapEmptyOneEq(0)
  <1>1. Seq({}) = {<<>>}
    BY SeqEmptyEq DEF Cases!SeqEmptyEq
  <1>2. <<>> \in Seq({1})
    <2>1. <<>> \in [1..0 -> {1}]
      OBVIOUS
    <2>2. 0 \in Nat
      OBVIOUS
    <2>3. QED BY <2>1, <2>2
  <1>3. QED BY <1>1, <1>2 DEF Cases!SeqCapEmptyOneEq

THEOREM FiniteSeqCapEmptyOne == Cases!FiniteSeqCapEmptyOne
  BY SeqCapEmptyOneEq, FS_Singleton
     DEF Cases!FiniteSeqCapEmptyOne, Cases!SeqCapEmptyOneEq

THEOREM FiniteSeqEmpty == Cases!FiniteSeqEmpty
  BY SeqEmptyEq, FS_Singleton
     DEF Cases!FiniteSeqEmpty, Cases!SeqEmptyEq

THEOREM CardSeqEmpty == Cases!CardSeqEmpty(0)
  BY SeqEmptyEq, FS_Singleton
     DEF Cases!CardSeqEmpty, Cases!SeqEmptyEq

THEOREM EnumSubsetSeqEmpty == Cases!EnumSubsetSeqEmpty
  BY EmptySeqInSeqEmpty
     DEF Cases!EnumSubsetSeqEmpty, Cases!EmptySeqInSeqEmpty

THEOREM SeqCapEmptyEnum == Cases!SeqCapEmptyEnum
  BY SeqEmptyEq DEF Cases!SeqCapEmptyEnum, Cases!SeqEmptyEq

THEOREM SeqCupEmpty == Cases!SeqCupEmpty
  BY DEF Cases!SeqCupEmpty

THEOREM EmptyInUnionSeq == Cases!EmptyInUnionSeq
  BY EmptySeqInSeqEmpty
     DEF Cases!EmptyInUnionSeq, Cases!EmptySeqInSeqEmpty

THEOREM CardSingletonRangeSeqEmpty == Cases!CardSingletonRangeSeqEmpty
  <1>1. [Seq({}) -> {0}] = {[x \in Seq({}) |-> 0]}
    OBVIOUS
  <1>2. QED BY <1>1, FS_Singleton DEF Cases!CardSingletonRangeSeqEmpty

THEOREM FiniteSeqEmptyFcnSet == Cases!FiniteSeqEmptyFcnSet
  <1>1. Seq({}) = {<<>>}
    BY SeqEmptyEq DEF Cases!SeqEmptyEq
  <1>2. [{<<>>} -> {1, 2}] = {[s \in {<<>>} |-> 1], [s \in {<<>>} |-> 2]}
    OBVIOUS
  <1>3. [s \in {<<>>} |-> 1] # [s \in {<<>>} |-> 2]
    OBVIOUS
  <1>4. QED BY <1>1, <1>2, <1>3, PairFiniteCardinality
            DEF Cases!FiniteSeqEmptyFcnSet

THEOREM FiniteSeqEmptyRcdSet == Cases!FiniteSeqEmptyRcdSet
  <1>1. Seq({}) = {<<>>}
    BY SeqEmptyEq DEF Cases!SeqEmptyEq
  <1>2. [a : {<<>>}] = {[a |-> <<>>]}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2, FS_Singleton DEF Cases!FiniteSeqEmptyRcdSet

THEOREM FiniteSeqEmptyProduct == Cases!FiniteSeqEmptyProduct
  <1>1. Seq({}) = {<<>>}
    BY SeqEmptyEq DEF Cases!SeqEmptyEq
  <1>2. {<<>>} \X {1} = {<<<<>>, 1>>}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2, FS_Singleton DEF Cases!FiniteSeqEmptyProduct

THEOREM SeqEmptySubsetSelf == Cases!SeqEmptySubsetSelf(0)
  BY DEF Cases!SeqEmptySubsetSelf

THEOREM SeqEmptySubsetEnum == Cases!SeqEmptySubsetEnum(0)
  BY SeqEmptyEq DEF Cases!SeqEmptySubsetEnum, Cases!SeqEmptyEq

THEOREM SeqEmptyExists == Cases!SeqEmptyExists(0)
  BY EmptySeqInSeqEmpty
     DEF Cases!SeqEmptyExists, Cases!EmptySeqInSeqEmpty

THEOREM UnionSeqEmpty == Cases!UnionSeqEmpty(0)
  BY SeqEmptyEq DEF Cases!UnionSeqEmpty, Cases!SeqEmptyEq

THEOREM CardSeqEmptyProduct == Cases!CardSeqEmptyProduct(0)
  <1>1. Seq({}) = {<<>>}
    BY SeqEmptyEq DEF Cases!SeqEmptyEq
  <1>2. {<<>>} \X {1} = {<<<<>>, 1>>}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2, FS_Singleton
            DEF Cases!CardSeqEmptyProduct

THEOREM CardSeqEmptyFcnSet == Cases!CardSeqEmptyFcnSet(0)
  <1>1. Seq({}) = {<<>>}
    BY SeqEmptyEq DEF Cases!SeqEmptyEq
  <1>2. [{<<>>} -> {1, 2}] = {[s \in {<<>>} |-> 1], [s \in {<<>>} |-> 2]}
    OBVIOUS
  <1>3. [s \in {<<>>} |-> 1] # [s \in {<<>>} |-> 2]
    OBVIOUS
  <1>4. QED BY <1>1, <1>2, <1>3, PairFiniteCardinality
            DEF Cases!CardSeqEmptyFcnSet

THEOREM CardSeqEmptyRcdSet == Cases!CardSeqEmptyRcdSet(0)
  <1>1. Seq({}) = {<<>>}
    BY SeqEmptyEq DEF Cases!SeqEmptyEq
  <1>2. [a : {<<>>}] = {[a |-> <<>>]}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2, FS_Singleton DEF Cases!CardSeqEmptyRcdSet

THEOREM EmptyInSubsetSeq == Cases!EmptyInSubsetSeq
  BY DEF Cases!EmptyInSubsetSeq

THEOREM SingletonInSubsetSeq == Cases!SingletonInSubsetSeq
  BY EmptySeqInSeqEmpty
     DEF Cases!SingletonInSubsetSeq, Cases!EmptySeqInSeqEmpty

THEOREM FiniteSubsetSeqEmpty == Cases!FiniteSubsetSeqEmpty
  <1>1. Seq({}) = {<<>>}
    BY SeqEmptyEq DEF Cases!SeqEmptyEq
  <1>2. SUBSET {<<>>} = {{}, {<<>>}}
    OBVIOUS
  <1>3. {} # {<<>>}
    OBVIOUS
  <1>4. QED BY <1>1, <1>2, <1>3, PairFiniteCardinality
            DEF Cases!FiniteSubsetSeqEmpty

THEOREM CardSubsetSeqEmpty == Cases!CardSubsetSeqEmpty(0)
  <1>1. Seq({}) = {<<>>}
    BY SeqEmptyEq DEF Cases!SeqEmptyEq
  <1>2. SUBSET {<<>>} = {{}, {<<>>}}
    OBVIOUS
  <1>3. {} # {<<>>}
    OBVIOUS
  <1>4. QED BY <1>1, <1>2, <1>3, PairFiniteCardinality
            DEF Cases!CardSubsetSeqEmpty

THEOREM EmptyStringInSTRING == Cases!EmptyStringInSTRING
  BY DEF Cases!EmptyStringInSTRING

THEOREM EnumSubsetNat == Cases!EnumSubsetNat
  BY DEF Cases!EnumSubsetNat

THEOREM EnumSubsetInt == Cases!EnumSubsetInt
  BY DEF Cases!EnumSubsetInt

THEOREM NatCupEmptyEqNat == Cases!NatCupEmptyEqNat
  BY DEF Cases!NatCupEmptyEqNat

THEOREM NatPairCupEmpty == Cases!NatPairCupEmpty
  BY NatCupEmptyEqNat, FS_Singleton
     DEF Cases!NatPairCupEmpty, Cases!NatCupEmptyEqNat

THEOREM ZeroInNatCupZero == Cases!ZeroInNatCupZero
  BY DEF Cases!ZeroInNatCupZero

THEOREM EnumSubsetNatCupZero == Cases!EnumSubsetNatCupZero
  BY DEF Cases!EnumSubsetNatCupZero

THEOREM OneInNatDiffZero == Cases!OneInNatDiffZero
  BY DEF Cases!OneInNatDiffZero

THEOREM ZeroNotInNatDiffZero == Cases!ZeroNotInNatDiffZero
  BY DEF Cases!ZeroNotInNatDiffZero

THEOREM EnumSubsetNatDiff == Cases!EnumSubsetNatDiff
  BY DEF Cases!EnumSubsetNatDiff

THEOREM ZeroInPredNat == Cases!ZeroInPredNat
  BY DEF Cases!ZeroInPredNat

THEOREM BoolMember == Cases!BoolMember
  BY DEF Cases!BoolMember

THEOREM BoolEqEnum == Cases!BoolEqEnum
  BY DEF Cases!BoolEqEnum

THEOREM CardBool == Cases!CardBool
  BY BoolEqEnum, PairFiniteCardinality
     DEF Cases!CardBool, Cases!BoolEqEnum

THEOREM FiniteBool == Cases!FiniteBool
  BY BoolEqEnum, PairFiniteCardinality
     DEF Cases!FiniteBool, Cases!BoolEqEnum

THEOREM ChooseBool == Cases!ChooseBool
  BY BoolEqEnum DEF Cases!ChooseBool, Cases!BoolEqEnum

THEOREM BoolSubsetEnum == Cases!BoolSubsetEnum
  BY BoolEqEnum DEF Cases!BoolSubsetEnum, Cases!BoolEqEnum

THEOREM EnumSubsetBool == Cases!EnumSubsetBool
  BY BoolEqEnum DEF Cases!EnumSubsetBool, Cases!BoolEqEnum

THEOREM BoolPredTrue == Cases!BoolPredTrue
  BY DEF Cases!BoolPredTrue

THEOREM CardBoolPredTrue == Cases!CardBoolPredTrue
  BY BoolPredTrue, FS_Singleton
     DEF Cases!CardBoolPredTrue, Cases!BoolPredTrue

THEOREM SubsetBoolEq == Cases!SubsetBoolEq
  BY BoolEqEnum DEF Cases!SubsetBoolEq, Cases!BoolEqEnum

THEOREM CardSubsetBool == Cases!CardSubsetBool
  BY SubsetBoolEq, QuadFiniteCardinality
     DEF Cases!CardSubsetBool, Cases!SubsetBoolEq

THEOREM FPBoolEnum == Cases!FPBoolEnum
  BY BoolEqEnum DEF Cases!FPBoolEnum, Cases!BoolEqEnum

THEOREM EmptyInSeqOne == Cases!EmptyInSeqOne
  <1>1. <<>> \in [1..0 -> {1}]
    OBVIOUS
  <1>2. 0 \in Nat
    OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF Cases!EmptyInSeqOne

THEOREM EnumSubsetSeqOne == Cases!EnumSubsetSeqOne
  BY DEF Cases!EnumSubsetSeqOne

THEOREM ZeroInNatCapNat == Cases!ZeroInNatCapNat
  BY DEF Cases!ZeroInNatCapNat

THEOREM EmptyInStringCap == Cases!EmptyInStringCap
  BY DEF Cases!EmptyInStringCap

THEOREM PairInNatProduct == Cases!PairInNatProduct
  BY DEF Cases!PairInNatProduct

THEOREM EnumSubsetNatProduct == Cases!EnumSubsetNatProduct
  BY PairInNatProduct
     DEF Cases!EnumSubsetNatProduct, Cases!PairInNatProduct

THEOREM CaseTrue == Cases!CaseTrue
  BY DEF Cases!CaseTrue

THEOREM CaseOther == Cases!CaseOther
  BY DEF Cases!CaseOther

THEOREM BoolPredFalse == Cases!BoolPredFalse
  BY DEF Cases!BoolPredFalse

THEOREM BoolIdApply == Cases!BoolIdApply
  BY DEF Cases!BoolIdApply

THEOREM RcdDomain == Cases!RcdDomain
  BY DEF Cases!RcdDomain

THEOREM RcdExcept == Cases!RcdExcept
  BY DEF Cases!RcdExcept

THEOREM TupleInSeqNat == Cases!TupleInSeqNat
  BY DEF Cases!TupleInSeqNat

THEOREM OneInIntCapNat == Cases!OneInIntCapNat
  BY DEF Cases!OneInIntCapNat

THEOREM EnumInSubsetNat == Cases!EnumInSubsetNat
  BY DEF Cases!EnumInSubsetNat

THEOREM LenTuple == Cases!LenTuple
  BY DEF Cases!LenTuple

THEOREM SubsetSingleton == Cases!SubsetSingleton
  BY DEF Cases!SubsetSingleton

THEOREM EmptyNeqString == Cases!EmptyNeqString
  BY DEF Cases!EmptyNeqString

THEOREM ChooseSingleton == Cases!ChooseSingleton
  BY DEF Cases!ChooseSingleton

THEOREM EmptyInSeqCapDisjoint == Cases!EmptyInSeqCapDisjoint
  <1>1. <<>> \in Seq({1})
    <2>1. <<>> \in [1..0 -> {1}]
      OBVIOUS
    <2>2. 0 \in Nat
      OBVIOUS
    <2>3. QED BY <2>1, <2>2
  <1>2. <<>> \in Seq({2})
    <2>1. <<>> \in [1..0 -> {2}]
      OBVIOUS
    <2>2. 0 \in Nat
      OBVIOUS
    <2>3. QED BY <2>1, <2>2
  <1>3. QED BY <1>1, <1>2 DEF Cases!EmptyInSeqCapDisjoint

THEOREM BoolCupTrue == Cases!BoolCupTrue
  BY DEF Cases!BoolCupTrue

THEOREM TrueCupBool == Cases!TrueCupBool
  BY DEF Cases!TrueCupBool

THEOREM UnionBool == Cases!UnionBool
  BY DEF Cases!UnionBool

THEOREM BoolSubsetSelf == Cases!BoolSubsetSelf
  BY DEF Cases!BoolSubsetSelf

THEOREM FourInBoundedPred == Cases!FourInBoundedPred
  BY DEF Cases!FourInBoundedPred

THEOREM FiveNotInBoundedPred == Cases!FiveNotInBoundedPred
  BY DEF Cases!FiveNotInBoundedPred

THEOREM EnumSubsetBoundedPred == Cases!EnumSubsetBoundedPred
  BY DEF Cases!EnumSubsetBoundedPred

THEOREM ZeroNotInNatDiffNat == Cases!ZeroNotInNatDiffNat
  BY DEF Cases!ZeroNotInNatDiffNat

THEOREM EnumDiffNatEmpty == Cases!EnumDiffNatEmpty
  BY DEF Cases!EnumDiffNatEmpty

THEOREM FiniteEnumDiffNat == Cases!FiniteEnumDiffNat
  BY EnumDiffNatEmpty, FS_EmptySet
     DEF Cases!FiniteEnumDiffNat, Cases!EnumDiffNatEmpty

THEOREM ThreeInIntervalCapNat == Cases!ThreeInIntervalCapNat
  BY DEF Cases!ThreeInIntervalCapNat

THEOREM IntervalCapNatEq == Cases!IntervalCapNatEq
  BY DEF Cases!IntervalCapNatEq

THEOREM FiniteIntervalCapNat == Cases!FiniteIntervalCapNat
  BY IntervalCapNatEq, FS_Interval
     DEF Cases!FiniteIntervalCapNat, Cases!IntervalCapNatEq

THEOREM PredOverEnumEq == Cases!PredOverEnumEq
  BY DEF Cases!PredOverEnumEq

THEOREM FinitePredOverEnum == Cases!FinitePredOverEnum
  BY PredOverEnumEq, FS_Interval
     DEF Cases!FinitePredOverEnum, Cases!PredOverEnumEq

THEOREM CardStringSingletonRange == Cases!CardStringSingletonRange
  <1>1. [STRING -> {0}] = {[x \in STRING |-> 0]}
    OBVIOUS
  <1>2. QED BY <1>1, FS_Singleton DEF Cases!CardStringSingletonRange

THEOREM FiniteStringSingletonRange == Cases!FiniteStringSingletonRange
  <1>1. [STRING -> {0}] = {[x \in STRING |-> 0]}
    OBVIOUS
  <1>2. QED BY <1>1, FS_Singleton DEF Cases!FiniteStringSingletonRange

THEOREM FcnDomainOrder == Cases!FcnDomainOrder
  BY DEF Cases!FcnDomainOrder

THEOREM NestedRcdExcept == Cases!NestedRcdExcept
  BY DEF Cases!NestedRcdExcept

THEOREM ConcatEmptyRight == Cases!ConcatEmptyRight
  BY DEF Cases!ConcatEmptyRight

THEOREM DivPos == Cases!DivPos
  BY SMT DEF Cases!DivPos

THEOREM ModPos == Cases!ModPos
  BY SMT DEF Cases!ModPos

THEOREM UnionIntervals == Cases!UnionIntervals
  BY DEF Cases!UnionIntervals

THEOREM NatIntSetPerm == Cases!NatIntSetPerm
  BY DEF Cases!NatIntSetPerm

THEOREM CardNatIntPair == Cases!CardNatIntPair
  <1>1. (-1) \in Int
    OBVIOUS
  <1>2. (-1) \notin Nat
    OBVIOUS
  <1>3. Nat # Int
    BY <1>1, <1>2
  <1>4. QED BY <1>3, PairFiniteCardinality DEF Cases!CardNatIntPair

THEOREM FcnSetBoolSingleton == Cases!FcnSetBoolSingleton
  BY DEF Cases!FcnSetBoolSingleton

THEOREM BoolZeroFcnMember == Cases!BoolZeroFcnMember
  BY FcnSetBoolSingleton
     DEF Cases!BoolZeroFcnMember, Cases!FcnSetBoolSingleton

THEOREM BoolZeroFcnForall == Cases!BoolZeroFcnForall
  BY FcnSetBoolSingleton
     DEF Cases!BoolZeroFcnForall, Cases!FcnSetBoolSingleton

THEOREM ChooseBoolFcn == Cases!ChooseBoolFcn
  BY FcnSetBoolSingleton
     DEF Cases!ChooseBoolFcn, Cases!FcnSetBoolSingleton

LEMMA BoolFcnSetFour ==
  [BOOLEAN -> {0, 1}] =
    {[x \in BOOLEAN |-> 0],
     [x \in BOOLEAN |-> IF x THEN 0 ELSE 1],
     [x \in BOOLEAN |-> IF x THEN 1 ELSE 0],
     [x \in BOOLEAN |-> 1]}
  BY BoolEqEnum DEF Cases!BoolEqEnum

THEOREM CardBoolFcnSet == Cases!CardBoolFcnSet
  <1>1. [x \in BOOLEAN |-> 0] # [x \in BOOLEAN |-> IF x THEN 0 ELSE 1]
    <2>1. [x \in BOOLEAN |-> 0][FALSE] = 0
      OBVIOUS
    <2>2. [x \in BOOLEAN |-> IF x THEN 0 ELSE 1][FALSE] = 1
      OBVIOUS
    <2>3. QED BY <2>1, <2>2
  <1>2. [x \in BOOLEAN |-> 0] # [x \in BOOLEAN |-> IF x THEN 1 ELSE 0]
    <2>1. [x \in BOOLEAN |-> 0][TRUE] = 0
      OBVIOUS
    <2>2. [x \in BOOLEAN |-> IF x THEN 1 ELSE 0][TRUE] = 1
      OBVIOUS
    <2>3. QED BY <2>1, <2>2
  <1>3. [x \in BOOLEAN |-> 0] # [x \in BOOLEAN |-> 1]
    <2>1. [x \in BOOLEAN |-> 0][TRUE] = 0
      OBVIOUS
    <2>2. [x \in BOOLEAN |-> 1][TRUE] = 1
      OBVIOUS
    <2>3. QED BY <2>1, <2>2
  <1>4. [x \in BOOLEAN |-> IF x THEN 0 ELSE 1]
        # [x \in BOOLEAN |-> IF x THEN 1 ELSE 0]
    <2>1. [x \in BOOLEAN |-> IF x THEN 0 ELSE 1][TRUE] = 0
      OBVIOUS
    <2>2. [x \in BOOLEAN |-> IF x THEN 1 ELSE 0][TRUE] = 1
      OBVIOUS
    <2>3. QED BY <2>1, <2>2
  <1>5. [x \in BOOLEAN |-> IF x THEN 0 ELSE 1] # [x \in BOOLEAN |-> 1]
    <2>1. [x \in BOOLEAN |-> IF x THEN 0 ELSE 1][TRUE] = 0
      OBVIOUS
    <2>2. [x \in BOOLEAN |-> 1][TRUE] = 1
      OBVIOUS
    <2>3. QED BY <2>1, <2>2
  <1>6. [x \in BOOLEAN |-> IF x THEN 1 ELSE 0] # [x \in BOOLEAN |-> 1]
    <2>1. [x \in BOOLEAN |-> IF x THEN 1 ELSE 0][FALSE] = 0
      OBVIOUS
    <2>2. [x \in BOOLEAN |-> 1][FALSE] = 1
      OBVIOUS
    <2>3. QED BY <2>1, <2>2
  <1>7. QED BY BoolFcnSetFour, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6,
               QuadFiniteCardinality
            DEF Cases!CardBoolFcnSet

THEOREM HeadTuple == Cases!HeadTuple
  BY DEF Cases!HeadTuple

THEOREM TailSingleton == Cases!TailSingleton
  BY DEF Cases!TailSingleton

THEOREM AppendEmpty == Cases!AppendEmpty
  BY DEF Cases!AppendEmpty

THEOREM ConcatTuples == Cases!ConcatTuples
  BY DEF Cases!ConcatTuples

THEOREM SubSeqEmpty == Cases!SubSeqEmpty
  BY DEF Cases!SubSeqEmpty

THEOREM LenEmptyTuple == Cases!LenEmptyTuple
  BY DEF Cases!LenEmptyTuple

THEOREM LenEmptyEnumFcn == Cases!LenEmptyEnumFcn
  BY EmptyEnumFcnEqTuple, LenEmptyTuple
     DEF Cases!LenEmptyEnumFcn, Cases!EmptyEnumFcnEqTuple,
         Cases!LenEmptyTuple

LEMMA CanonicalEmptyFcnEqTuple == [x \in 1..0 |-> x] = <<>>
  BY EmptyCanonicalVsOtherInterval, EmptyIntervalFcnEqTuple
     DEF Cases!EmptyCanonicalVsOtherInterval,
         Cases!EmptyIntervalFcnEqTuple

THEOREM LenCanonicalEmptyFcn == Cases!LenCanonicalEmptyFcn
  BY CanonicalEmptyFcnEqTuple, LenEmptyTuple
     DEF Cases!LenCanonicalEmptyFcn, Cases!LenEmptyTuple

THEOREM AppendCanonicalEmptyFcn == Cases!AppendCanonicalEmptyFcn
  BY CanonicalEmptyFcnEqTuple, AppendEmpty
     DEF Cases!AppendCanonicalEmptyFcn, Cases!AppendEmpty

THEOREM EmptyEnumFcnInSeqEmpty == Cases!EmptyEnumFcnInSeqEmpty
  BY EmptyEnumFcnEqTuple, EmptySeqInSeqEmpty
     DEF Cases!EmptyEnumFcnInSeqEmpty, Cases!EmptyEnumFcnEqTuple,
         Cases!EmptySeqInSeqEmpty

THEOREM NegEmptyInterval == Cases!NegEmptyInterval
  BY DEF Cases!NegEmptyInterval

THEOREM CardNegEmptyInterval == Cases!CardNegEmptyInterval
  BY NegEmptyInterval, FS_EmptySet
     DEF Cases!CardNegEmptyInterval, Cases!NegEmptyInterval

THEOREM LambdaExcept == Cases!LambdaExcept
  BY DEF Cases!LambdaExcept

THEOREM NatCupZeroEqNat == Cases!NatCupZeroEqNat(0)
  BY DEF Cases!NatCupZeroEqNat

THEOREM NatCupZeroRefl == Cases!NatCupZeroRefl(0)
  BY DEF Cases!NatCupZeroRefl

THEOREM NatDiffZeroRefl == Cases!NatDiffZeroRefl(0)
  BY DEF Cases!NatDiffZeroRefl

THEOREM UnionNatEqNat == Cases!UnionNatEqNat(0)
  BY DEF Cases!UnionNatEqNat

THEOREM NatPairCupZero == Cases!NatPairCupZero(0)
  BY NatCupZeroEqNat, FS_Singleton
     DEF Cases!NatPairCupZero, Cases!NatCupZeroEqNat

THEOREM PredNatEqNat == Cases!PredNatEqNat(0)
  BY DEF Cases!PredNatEqNat

THEOREM NatSubsetNat == Cases!NatSubsetNat(0)
  BY DEF Cases!NatSubsetNat

THEOREM NatZeroFcnMember == Cases!NatZeroFcnMember(0)
  BY DEF Cases!NatZeroFcnMember

THEOREM NatZeroFcnForall == Cases!NatZeroFcnForall(0)
  <1>1. [Nat -> {0}] = {[x \in Nat |-> 0]}
    OBVIOUS
  <1>2. [x \in Nat |-> 0][0] = 0
    BY NatZeroFcnApply DEF Cases!NatZeroFcnApply
  <1>3. QED BY <1>1, <1>2 DEF Cases!NatZeroFcnForall

THEOREM FcnSetNatCupZero == Cases!FcnSetNatCupZero(0)
  BY NatCupZeroEqNat
     DEF Cases!FcnSetNatCupZero, Cases!NatCupZeroEqNat

THEOREM NatExceptExt == Cases!NatExceptExt(0)
  BY DEF Cases!NatExceptExt

THEOREM NatNeqSingleton == Cases!NatNeqSingleton(0)
  <1>1. 0 \in Nat
    OBVIOUS
  <1>2. 0 \notin {1}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF Cases!NatNeqSingleton

THEOREM EmptyNeqNat == Cases!EmptyNeqNat(0)
  <1>1. 0 \in Nat
    OBVIOUS
  <1>2. 0 \notin {}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF Cases!EmptyNeqNat

THEOREM NatCapNatEq == Cases!NatCapNatEq(0)
  BY DEF Cases!NatCapNatEq

THEOREM SeqOneSubsetSeqTwo == Cases!SeqOneSubsetSeqTwo(0)
  <1> SUFFICES ASSUME NEW s \in Seq({1})
               PROVE  s \in Seq({1, 2})
    BY DEF Cases!SeqOneSubsetSeqTwo
  <1>1. PICK n \in Nat : s \in [1..n -> {1}]
    OBVIOUS
  <1>2. s \in [1..n -> {1}]
    BY <1>1
  <1>3. DOMAIN s = 1..n
    BY <1>2, SMT
  <1>4. \A i \in 1..n : s[i] \in {1}
    BY <1>2, SMT
  <1>5. \A i \in 1..n : s[i] \in {1, 2}
    BY <1>4
  <1>6. s \in [1..n -> {1, 2}]
    BY <1>3, <1>5
  <1>7. QED BY <1>1, <1>6

THEOREM SeqCapDisjointEq == Cases!SeqCapDisjointEq(0)
  <1>1. <<>> \in Seq({1}) \cap Seq({2})
    BY EmptyInSeqCapDisjoint DEF Cases!EmptyInSeqCapDisjoint
  <1> SUFFICES ASSUME NEW s \in Seq({1}) \cap Seq({2})
               PROVE  s = <<>>
    BY <1>1 DEF Cases!SeqCapDisjointEq
  <1>2. PICK n \in Nat : s \in [1..n -> {1}]
    OBVIOUS
  <1>3. s \in [1..n -> {1}]
    BY <1>2
  <1>4. PICK m \in Nat : s \in [1..m -> {2}]
    OBVIOUS
  <1>5. s \in [1..m -> {2}]
    BY <1>4
  <1>6. DOMAIN s = 1..n
    BY <1>3, SMT
  <1>7. DOMAIN s = 1..m
    BY <1>5, SMT
  <1>8. n = m
    BY <1>6, <1>7
  <1>9. ASSUME n # 0
        PROVE  FALSE
    <2>1. 1 \in 1..n
      BY <1>9
    <2>2. s[1] \in {1}
      BY <1>3, <2>1, SMT
    <2>3. s[1] \in {2}
      BY <1>5, <1>8, <2>1, SMT
    <2>4. QED BY <2>2, <2>3
  <1>10. n = 0
    BY <1>9
  <1>11. QED BY <1>3, <1>10

THEOREM FiniteSeqCapDisjoint == Cases!FiniteSeqCapDisjoint(0)
  BY SeqCapDisjointEq, FS_Singleton
     DEF Cases!FiniteSeqCapDisjoint, Cases!SeqCapDisjointEq

THEOREM NatSubsetInt == Cases!NatSubsetInt(0)
  BY DEF Cases!NatSubsetInt

THEOREM IntCapNatEq == Cases!IntCapNatEq(0)
  BY DEF Cases!IntCapNatEq

THEOREM StringNeqEmpty == Cases!StringNeqEmpty(0)
  <1>1. "" \in STRING
    BY EmptyStringInSTRING DEF Cases!EmptyStringInSTRING
  <1>2. "a" \in STRING
    OBVIOUS
  <1>3. "" # "a"
    BY EmptyNeqString DEF Cases!EmptyNeqString
  <1>4. "a" \notin {""}
    BY <1>3
  <1>5. QED BY <1>2, <1>4 DEF Cases!StringNeqEmpty

THEOREM BoundedPredEq == Cases!BoundedPredEq(0)
  BY SMT DEF Cases!BoundedPredEq

THEOREM FiniteBoundedPred == Cases!FiniteBoundedPred(0)
  <1>1. {x \in Nat : x < 5} \in SUBSET Nat
    OBVIOUS
  <1>2. \A s \in {x \in Nat : x < 5} : s <= 4
    OBVIOUS
  <1>3. QED BY <1>1, <1>2, FS_BoundedSetOfNaturals
            DEF Cases!FiniteBoundedPred

THEOREM CardBoundedPred == Cases!CardBoundedPred(0)
  <1>1. {x \in Nat : x < 5} = 0..4
    BY BoundedPredEq DEF Cases!BoundedPredEq
  <1>2. Cardinality(0..4) = 5
    BY FS_Interval
  <1>3. QED BY <1>1, <1>2 DEF Cases!CardBoundedPred

THEOREM ExistsBoundedPred == Cases!ExistsBoundedPred(0)
  BY FourInBoundedPred
     DEF Cases!ExistsBoundedPred, Cases!FourInBoundedPred

THEOREM FiniteNatDiffNat == Cases!FiniteNatDiffNat(0)
  <1>1. Nat \ Nat = {}
    OBVIOUS
  <1>2. QED BY <1>1, FS_EmptySet DEF Cases!FiniteNatDiffNat

THEOREM StringZeroFcnMember == Cases!StringZeroFcnMember(0)
  <1>1. [STRING -> {0}] = {[x \in STRING |-> 0]}
    OBVIOUS
  <1>2. QED BY <1>1 DEF Cases!StringZeroFcnMember

THEOREM DivNegDividend == Cases!DivNegDividend
  BY SMT DEF Cases!DivNegDividend

THEOREM ModNegDividend == Cases!ModNegDividend
  BY SMT DEF Cases!ModNegDividend

THEOREM FiniteNatCapEmpty == Cases!FiniteNatCapEmpty
  <1>1. Nat \cap {} = {}
    OBVIOUS
  <1>2. QED BY <1>1, FS_EmptySet DEF Cases!FiniteNatCapEmpty

THEOREM FiniteEmptyDiffNat == Cases!FiniteEmptyDiffNat
  <1>1. {} \ Nat = {}
    OBVIOUS
  <1>2. QED BY <1>1, FS_EmptySet DEF Cases!FiniteEmptyDiffNat

THEOREM OneInUnionNat == Cases!OneInUnionNat
  <1>1. 1 \in Nat
    OBVIOUS
  <1>2. Nat \in {Nat}
    OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF Cases!OneInUnionNat

THEOREM VacuousForall == Cases!VacuousForall
  BY DEF Cases!VacuousForall

THEOREM EmptyExists == Cases!EmptyExists
  BY DEF Cases!EmptyExists

THEOREM RecordPermutation == Cases!RecordPermutation
  BY DEF Cases!RecordPermutation

THEOREM TupleReflexive == Cases!TupleReflexive
  BY DEF Cases!TupleReflexive

THEOREM TupleDomainDiffer == Cases!TupleDomainDiffer
  BY DEF Cases!TupleDomainDiffer

THEOREM IntervalReflexive == Cases!IntervalReflexive
  BY DEF Cases!IntervalReflexive

THEOREM IntervalDiffer == Cases!IntervalDiffer
  BY DEF Cases!IntervalDiffer

THEOREM SubsetIntervalEq == Cases!SubsetIntervalEq
  BY IntervalEqEnum DEF Cases!SubsetIntervalEq, Cases!IntervalEqEnum

THEOREM SubsetIntervalEqRev == Cases!SubsetIntervalEqRev
  BY SubsetIntervalEq
     DEF Cases!SubsetIntervalEqRev, Cases!SubsetIntervalEq

THEOREM CapLazyEqEnum == Cases!CapLazyEqEnum
  BY DEF Cases!CapLazyEqEnum

THEOREM CupLazyEqEnum == Cases!CupLazyEqEnum
  BY DEF Cases!CupLazyEqEnum

LEMMA SubsetSingletonTwo == SUBSET {2} = {{}, {2}}
  OBVIOUS

THEOREM DiffLazyEqEnum == Cases!DiffLazyEqEnum
  BY SubsetEqEnum, SubsetSingletonTwo
     DEF Cases!DiffLazyEqEnum, Cases!SubsetEqEnum

THEOREM UnionLazyEqEnum == Cases!UnionLazyEqEnum
  BY DEF Cases!UnionLazyEqEnum

THEOREM PredEquivalent == Cases!PredEquivalent
  BY SMT DEF Cases!PredEquivalent

THEOREM FcnSetStructuralEq == Cases!FcnSetStructuralEq
  BY DEF Cases!FcnSetStructuralEq

THEOREM FcnSetStructuralDiff == Cases!FcnSetStructuralDiff
  <1>1. [x \in 1..2 |-> 1] \in [1..2 -> {1}]
    OBVIOUS
  <1>2. [x \in 1..2 |-> 1] \notin [1..2 -> {2}]
    OBVIOUS
  <1>3. QED BY <1>1, <1>2 DEF Cases!FcnSetStructuralDiff

THEOREM RcdSetPermutation == Cases!RcdSetPermutation
  BY DEF Cases!RcdSetPermutation

THEOREM TupleSetStructuralEq == Cases!TupleSetStructuralEq
  BY DEF Cases!TupleSetStructuralEq

THEOREM NatDiffInt == Cases!NatDiffInt
  BY DEF Cases!NatDiffInt

THEOREM IntDiffNat == Cases!IntDiffNat
  BY NatDiffInt DEF Cases!IntDiffNat, Cases!NatDiffInt

THEOREM StringInStringSet == Cases!StringInStringSet
  BY DEF Cases!StringInStringSet

THEOREM EnumQuantifiers == Cases!EnumQuantifiers
  BY DEF Cases!EnumQuantifiers

THEOREM IntervalQuantifiers == Cases!IntervalQuantifiers
  BY DEF Cases!IntervalQuantifiers

THEOREM SubsetQuantifiers == Cases!SubsetQuantifiers
  BY DEF Cases!SubsetQuantifiers

THEOREM CapQuantifiers == Cases!CapQuantifiers
  BY DEF Cases!CapQuantifiers

THEOREM DiffQuantifiers == Cases!DiffQuantifiers
  BY DEF Cases!DiffQuantifiers

THEOREM CupQuantifiers == Cases!CupQuantifiers
  BY DEF Cases!CupQuantifiers

THEOREM UnionQuantifiers == Cases!UnionQuantifiers
  BY DEF Cases!UnionQuantifiers

THEOREM PredQuantifiers == Cases!PredQuantifiers
  BY DEF Cases!PredQuantifiers

THEOREM FcnSetQuantifiers == Cases!FcnSetQuantifiers
  <1>1. [{} -> {1}] = {<<>>}
    OBVIOUS
  <1>2. QED BY <1>1 DEF Cases!FcnSetQuantifiers

THEOREM RcdSetQuantifiers == Cases!RcdSetQuantifiers
  BY DEF Cases!RcdSetQuantifiers

THEOREM TupleSetQuantifiers == Cases!TupleSetQuantifiers
  BY DEF Cases!TupleSetQuantifiers

THEOREM ChooseIntervalEnum == Cases!ChooseIntervalEnum
  BY IntervalEqEnum
     DEF Cases!ChooseIntervalEnum, Cases!IntervalEqEnum

THEOREM ChooseSubsetEnum == Cases!ChooseSubsetEnum
  BY SubsetEqEnum
     DEF Cases!ChooseSubsetEnum, Cases!SubsetEqEnum

THEOREM ChooseCapEnum == Cases!ChooseCapEnum
  BY CapEqEnum DEF Cases!ChooseCapEnum, Cases!CapEqEnum

THEOREM ChooseDiffEnum == Cases!ChooseDiffEnum
  BY DiffEqEnum DEF Cases!ChooseDiffEnum, Cases!DiffEqEnum

THEOREM ChooseCupEnum == Cases!ChooseCupEnum
  BY LazyCupEqEnum
     DEF Cases!ChooseCupEnum, Cases!LazyCupEqEnum

THEOREM ChooseUnionEnum == Cases!ChooseUnionEnum
  BY UnionPower DEF Cases!ChooseUnionEnum, Cases!UnionPower

THEOREM ChoosePredEnum == Cases!ChoosePredEnum
  BY PredEqEnum DEF Cases!ChoosePredEnum, Cases!PredEqEnum

THEOREM ChooseFcnSetEnum == Cases!ChooseFcnSetEnum
  BY FcnSetEqEnum
     DEF Cases!ChooseFcnSetEnum, Cases!FcnSetEqEnum

THEOREM ChooseRcdSetEnum == Cases!ChooseRcdSetEnum
  BY RcdSetEqEnum
     DEF Cases!ChooseRcdSetEnum, Cases!RcdSetEqEnum

THEOREM ChooseTupleSetEnum == Cases!ChooseTupleSetEnum
  BY TupleSetEqEnum
     DEF Cases!ChooseTupleSetEnum, Cases!TupleSetEqEnum

THEOREM MaxIntervalSubset == Cases!MaxIntervalSubset(0)
  BY DEF Cases!MaxIntervalSubset, Cases!MaxInterval, Cases!MaxInt

THEOREM MaxIntervalDiff == Cases!MaxIntervalDiff(0)
  BY DEF Cases!MaxIntervalDiff, Cases!MaxInterval, Cases!MaxInt

THEOREM MaxIntervalCap == Cases!MaxIntervalCap(0)
  BY DEF Cases!MaxIntervalCap, Cases!MaxInterval, Cases!MaxInt

THEOREM MaxIntervalCup == Cases!MaxIntervalCup(0)
  BY DEF Cases!MaxIntervalCup, Cases!MaxInterval, Cases!MaxInt

THEOREM MaxIntervalPred == Cases!MaxIntervalPred(0)
  BY DEF Cases!MaxIntervalPred, Cases!MaxInterval, Cases!MaxInt

THEOREM FPMaxInterval == Cases!FPMaxInterval(0)
  BY MaxIntervalSubset
     DEF Cases!FPMaxInterval, Cases!MaxIntervalSubset,
         Cases!MaxInterval, Cases!MaxInt

THEOREM MaxIntervalExists == Cases!MaxIntervalExists
  BY DEF Cases!MaxIntervalExists, Cases!MaxInterval,
         Cases!MaxInt, Cases!MinInt

THEOREM MaxIntervalForall == Cases!MaxIntervalForall
  BY DEF Cases!MaxIntervalForall, Cases!MaxInterval, Cases!MaxInt

THEOREM MaxIntervalChoose == Cases!MaxIntervalChoose
  BY DEF Cases!MaxIntervalChoose, Cases!MaxInterval, Cases!MaxInt

THEOREM MaxIntervalEqEnum == Cases!MaxIntervalEqEnum
  BY DEF Cases!MaxIntervalEqEnum, Cases!MaxInterval, Cases!MaxInt

THEOREM MaxEnumSubsetInterval == Cases!MaxEnumSubsetInterval
  BY DEF Cases!MaxEnumSubsetInterval, Cases!MaxInterval, Cases!MaxInt

THEOREM MaxIntervalReflexiveSubset == Cases!MaxIntervalReflexiveSubset
  BY DEF Cases!MaxIntervalReflexiveSubset, Cases!MaxInterval, Cases!MaxInt

THEOREM CardMaxIntervalPair == Cases!CardMaxIntervalPair
  BY MaxIntervalEqEnum, FS_Singleton
     DEF Cases!CardMaxIntervalPair, Cases!MaxIntervalEqEnum,
         Cases!MaxInterval, Cases!MaxInt

THEOREM CardSubsetMaxInterval == Cases!CardSubsetMaxInterval
  <1>1. Cases!MaxInterval = {Cases!MaxInt}
    BY MaxIntervalEqEnum
       DEF Cases!MaxIntervalEqEnum, Cases!MaxInterval, Cases!MaxInt
  <1>2. SUBSET {Cases!MaxInt} = {{}, {Cases!MaxInt}}
    OBVIOUS
  <1>3. {} # {Cases!MaxInt}
    BY DEF Cases!MaxInt
  <1>4. QED BY <1>1, <1>2, <1>3, PairFiniteCardinality
            DEF Cases!CardSubsetMaxInterval, Cases!MaxInterval,
                Cases!MaxInt

THEOREM MaxIntervalFcnApply == Cases!MaxIntervalFcnApply
  BY DEF Cases!MaxIntervalFcnApply, Cases!MaxInt

THEOREM CardMaxInterval == Cases!CardMaxInterval
  BY MaxIntervalEqEnum, FS_Singleton
     DEF Cases!CardMaxInterval, Cases!MaxIntervalEqEnum,
         Cases!MaxInterval, Cases!MaxInt

THEOREM MaxIntInMaxInterval == Cases!MaxIntInMaxInterval
  BY DEF Cases!MaxIntInMaxInterval, Cases!MaxInterval, Cases!MaxInt

THEOREM MinIntNotInMaxInterval == Cases!MinIntNotInMaxInterval
  BY DEF Cases!MinIntNotInMaxInterval, Cases!MaxInterval,
         Cases!MaxInt, Cases!MinInt

THEOREM EmptyInSubsetMax == Cases!EmptyInSubsetMax
  BY DEF Cases!EmptyInSubsetMax, Cases!MaxInterval, Cases!MaxInt

THEOREM MaxSingletonInSubsetMax == Cases!MaxSingletonInSubsetMax
  BY DEF Cases!MaxSingletonInSubsetMax, Cases!MaxInterval, Cases!MaxInt

THEOREM MinSingletonNotInSubsetMax == Cases!MinSingletonNotInSubsetMax
  BY DEF Cases!MinSingletonNotInSubsetMax, Cases!MaxInterval,
         Cases!MaxInt, Cases!MinInt

THEOREM MinIntInSingleton == Cases!MinIntInSingleton
  BY DEF Cases!MinIntInSingleton, Cases!MinInt

THEOREM MinIntervalEq == Cases!MinIntervalEq
  BY DEF Cases!MinIntervalEq, Cases!MinInt

THEOREM CardMinInterval == Cases!CardMinInterval
  BY MinIntervalEq, FS_Singleton
     DEF Cases!CardMinInterval, Cases!MinIntervalEq, Cases!MinInt

THEOREM MaxIntervalFcnEq == Cases!MaxIntervalFcnEq(0)
  BY MaxIntervalEqEnum
     DEF Cases!MaxIntervalFcnEq, Cases!MaxIntervalEqEnum,
         Cases!MaxInterval, Cases!MaxInt

THEOREM MaxIntervalFcnMember == Cases!MaxIntervalFcnMember(0)
  BY MaxIntervalFcnEq
     DEF Cases!MaxIntervalFcnMember, Cases!MaxIntervalFcnEq,
         Cases!MaxInterval, Cases!MaxInt

\* Stated over an opaque n because a backend that sees the MaxInt literal in
\* an interval times out on the function equality.
LEMMA CombineSingletonInterval ==
  ASSUME NEW n, NEW a, NEW b, n..n = {n}
  PROVE  /\ [x \in (DOMAIN [y \in n..n |-> a]) \cup (DOMAIN [y \in {n} |-> b])
               |-> IF x \in DOMAIN [y \in n..n |-> a]
                     THEN [y \in n..n |-> a][x]
                     ELSE [y \in {n} |-> b][x]]
            = [x \in {n} |-> a]
         /\ [x \in (DOMAIN [y \in {n} |-> a]) \cup (DOMAIN [y \in n..n |-> b])
               |-> IF x \in DOMAIN [y \in {n} |-> a]
                     THEN [y \in {n} |-> a][x]
                     ELSE [y \in n..n |-> b][x]]
            = [x \in {n} |-> a]
  OBVIOUS

THEOREM MaxIntervalFcnCombine == Cases!MaxIntervalFcnCombine(0)
  <1>1. Cases!MaxInt..Cases!MaxInt = {Cases!MaxInt}
    BY MaxIntervalEqEnum DEF Cases!MaxIntervalEqEnum, Cases!MaxInterval
  <1>2. QED BY <1>1, CombineSingletonInterval
    DEF Cases!MaxIntervalFcnCombine

THEOREM MaxIntervalFcnCombineRev == Cases!MaxIntervalFcnCombineRev(0)
  <1>1. Cases!MaxInt..Cases!MaxInt = {Cases!MaxInt}
    BY MaxIntervalEqEnum DEF Cases!MaxIntervalEqEnum, Cases!MaxInterval
  <1>2. QED BY <1>1, CombineSingletonInterval
    DEF Cases!MaxIntervalFcnCombineRev

THEOREM MaxPredExists == Cases!MaxPredExists(0)
  BY DEF Cases!MaxPredExists, Cases!IdentityPred,
         Cases!MaxInterval, Cases!MaxInt, Cases!MinInt

THEOREM MaxPredForall == Cases!MaxPredForall(0)
  BY DEF Cases!MaxPredForall, Cases!IdentityPred,
         Cases!MaxInterval, Cases!MaxInt

THEOREM MaxCapExists == Cases!MaxCapExists(0)
  BY DEF Cases!MaxCapExists, Cases!IdentityPred,
         Cases!MaxInterval, Cases!MaxInt, Cases!MinInt

THEOREM MaxCupExists == Cases!MaxCupExists(0)
  BY DEF Cases!MaxCupExists, Cases!IdentityPred,
         Cases!MaxInterval, Cases!MaxInt, Cases!MinInt

THEOREM MaxDiffExists == Cases!MaxDiffExists(0)
  BY DEF Cases!MaxDiffExists, Cases!IdentityPred,
         Cases!MaxInterval, Cases!MaxInt, Cases!MinInt

THEOREM MaxUnionExists == Cases!MaxUnionExists(0)
  BY DEF Cases!MaxUnionExists, Cases!IdentityPred,
         Cases!MaxInterval, Cases!MaxInt, Cases!MinInt

THEOREM MaxTupleSetExists == Cases!MaxTupleSetExists(0)
  BY DEF Cases!MaxTupleSetExists, Cases!IdentityPred,
         Cases!MaxInterval, Cases!MaxInt, Cases!MinInt

THEOREM MaxRcdSetExists == Cases!MaxRcdSetExists(0)
  BY DEF Cases!MaxRcdSetExists, Cases!IdentityPred,
         Cases!MaxInterval, Cases!MaxInt, Cases!MinInt

THEOREM MaxFcnSetExists == Cases!MaxFcnSetExists(0)
  BY DEF Cases!MaxFcnSetExists, Cases!IdentityPred,
         Cases!MaxInterval, Cases!MaxInt, Cases!MinInt

THEOREM InfiniteCapEmpty == Cases!InfiniteCapEmpty(0)
  BY DEF Cases!InfiniteCapEmpty

THEOREM InfiniteDiffEmpty == Cases!InfiniteDiffEmpty(0)
  BY DEF Cases!InfiniteDiffEmpty

THEOREM InfinitePredEmpty == Cases!InfinitePredEmpty(0)
  BY DEF Cases!InfinitePredEmpty

THEOREM FiniteInfinitePredEmpty == Cases!FiniteInfinitePredEmpty(0)
  BY InfinitePredEmpty, FS_EmptySet
     DEF Cases!FiniteInfinitePredEmpty, Cases!InfinitePredEmpty

THEOREM FiniteCupInfinitePredEmpty == Cases!FiniteCupInfinitePredEmpty(0)
  BY InfinitePredEmpty, FS_Singleton
     DEF Cases!FiniteCupInfinitePredEmpty, Cases!InfinitePredEmpty

THEOREM FiniteUnionInfinitePredEmpty == Cases!FiniteUnionInfinitePredEmpty(0)
  BY InfinitePredEmpty, FS_EmptySet
     DEF Cases!FiniteUnionInfinitePredEmpty, Cases!InfinitePredEmpty

THEOREM MixedEmptyFcnApplyTuple == Cases!MixedEmptyFcnApplyTuple
  BY EmptyIntervalFcnEqTuple
     DEF Cases!MixedEmptyFcnApplyTuple, Cases!MixedEmptyDomFcn,
         Cases!EmptyIntervalFcnEqTuple

THEOREM MixedEmptyFcnApplyInterval == Cases!MixedEmptyFcnApplyInterval
  BY EmptyIntervalFcnEqTuple
     DEF Cases!MixedEmptyFcnApplyInterval, Cases!MixedEmptyDomFcn,
         Cases!EmptyIntervalFcnEqTuple

THEOREM MixedEmptyFcnEq == Cases!MixedEmptyFcnEq(0)
  BY EmptyIntervalFcnEqTuple
     DEF Cases!MixedEmptyFcnEq, Cases!MixedEmptyDomFcn,
         Cases!SingletonEmptyDomFcn, Cases!EmptyIntervalFcnEqTuple

THEOREM MixedEmptyFcnDomainEq == Cases!MixedEmptyFcnDomainEq(0)
  BY EmptyIntervalFcnEqTuple
     DEF Cases!MixedEmptyFcnDomainEq, Cases!MixedEmptyDomFcn,
         Cases!EmptyIntervalFcnEqTuple

THEOREM MixedEmptyFcnDomainCard == Cases!MixedEmptyFcnDomainCard(0)
  BY MixedEmptyFcnDomainEq, FS_Singleton
     DEF Cases!MixedEmptyFcnDomainCard, Cases!MixedEmptyFcnDomainEq,
         Cases!MixedEmptyDomFcn, Cases!EmptyIntervalFcnEqTuple

THEOREM LenEmptyIntervalFcn == Cases!LenEmptyIntervalFcn(0)
  BY EmptyIntervalFcnEqTuple, LenEmptyTuple
     DEF Cases!LenEmptyIntervalFcn, Cases!EmptyIntervalFcnEqTuple,
         Cases!LenEmptyTuple

THEOREM AppendEmptyIntervalFcn == Cases!AppendEmptyIntervalFcn(0)
  BY EmptyIntervalFcnEqTuple, AppendEmpty
     DEF Cases!AppendEmptyIntervalFcn, Cases!EmptyIntervalFcnEqTuple,
         Cases!AppendEmpty

THEOREM ConcatEmptyIntervalFcn == Cases!ConcatEmptyIntervalFcn(0)
  <1>1. <<>> \o <<1>> = <<1>>
    OBVIOUS
  <1>2. QED BY <1>1, EmptyIntervalFcnEqTuple
    DEF Cases!ConcatEmptyIntervalFcn, Cases!EmptyIntervalFcnEqTuple

THEOREM EmptyIntervalFcnInSeqEmpty == Cases!EmptyIntervalFcnInSeqEmpty(0)
  BY EmptyIntervalFcnEqTuple, EmptySeqInSeqEmpty
     DEF Cases!EmptyIntervalFcnInSeqEmpty, Cases!EmptyIntervalFcnEqTuple,
         Cases!EmptySeqInSeqEmpty
=============================================================================
