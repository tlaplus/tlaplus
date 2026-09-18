------------------------ MODULE ValueSemanticsCases -------------------------
\* Shared, assumption-free propositions about standard TLA+ value semantics.
EXTENDS Integers, Sequences

CONSTANTS Cardinality(_), IsFiniteSet(_), Fingerprint(_), Combine(_, _), Model

-----------------------------------------------------------------------------
\* Atomic and explicitly enumerated values: IntValue, StringValue, BoolValue, ModelValue, and SetEnumValue.

IntReflexive          == 1 = 1
IntNestedDuplicate    == Cardinality({1, 1}) = 1
StringReflexive       == "a" = "a"
StringNestedDuplicate == Cardinality({"a", "a"}) = 1
BoolReflexive         == TRUE = TRUE
BoolNestedDuplicate   == Cardinality({TRUE, TRUE}) = 1
ModelReflexive        == Model = Model
ModelNestedDuplicate  == Cardinality({Model, Model}) = 1

EnumPermutation   == {3, 1, 2} = {2, 3, 1}
EnumDuplicates    == {1, 2, 1, 2} = {1, 2}
EnumMember        == 2 \in {1, 2, 3}
EnumNotMember     == 4 \notin {1, 2, 3}
CardEnum          == Cardinality({1, 2, 3}) = 3
FiniteEnum        == IsFiniteSet({1, 2, 3})
FPEnumPermutation == Fingerprint({3, 1, 2}) = Fingerprint({2, 3, 1})

-----------------------------------------------------------------------------
\* IntervalValue.

IntervalEqEnum    == 1..3 = {1, 2, 3}
EnumEqInterval    == {1, 2, 3} = 1..3
IntervalNested    == Cardinality({1..3, {1, 2, 3}}) = 1
IntervalDuplicate == Cardinality({1..3, 1..3}) = 1
IntervalMember    == 2 \in 1..3
IntervalNotMember == 4 \notin 1..3
CardInterval      == Cardinality(1..3) = 3
FiniteInterval    == IsFiniteSet(1..3)
FPIntervalEnum    == Fingerprint(1..3) = Fingerprint({1, 2, 3})

-----------------------------------------------------------------------------
\* SubsetValue. KSubsetValue has its own KSubset* suite.

SubsetEqEnum              == SUBSET {1, 2} = {{}, {1}, {2}, {1, 2}}
EnumEqSubset              == {{}, {1}, {2}, {1, 2}} = SUBSET {1, 2}
SubsetNested              == Cardinality({SUBSET {1, 2}, {{}, {1}, {2}, {1, 2}}}) = 1
SubsetBaseDuplicate       == SUBSET {1, 1, 2} = SUBSET {1, 2}
SubsetBaseDuplicateNested == Cardinality({SUBSET {1, 1, 2}, SUBSET {1, 2}}) = 1
SubsetMember              == {1} \in SUBSET {1, 2}
SubsetNotMember           == {3} \notin SUBSET {1, 2}
CardSubset                == Cardinality(SUBSET {1, 2}) = 4
FiniteSubset              == IsFiniteSet(SUBSET {1, 2})
FPSubsetEnum              == Fingerprint(SUBSET {1, 2}) = Fingerprint({{}, {1}, {2}, {1, 2}})

-----------------------------------------------------------------------------
\* SetCapValue.

CapEqEnum    == Nat \cap {1, 2} = {1, 2}
EnumEqCap    == {1, 2} = Nat \cap {1, 2}
CapNested    == Cardinality({Nat \cap {1, 2}, {1, 2}}) = 1
CapSym       == Nat \cap {1, 2} = {1, 2} \cap Nat
CapSymNested == Cardinality({Nat \cap {1, 2}, {1, 2} \cap Nat}) = 1
CapMember    == 1 \in Nat \cap {1, 2}
CapNotMember == 3 \notin Nat \cap {1, 2}
CardCap      == Cardinality(Nat \cap {1, 2}) = 2
FiniteCap    == IsFiniteSet(Nat \cap {1, 2})
FPCapEnum    == Fingerprint(Nat \cap {1, 2}) = Fingerprint({1, 2})

-----------------------------------------------------------------------------
\* SetDiffValue, including a SetPredValue left operand that prevents eager reduction by IntervalValue.

DiffEqEnum        == (1..4) \ {2, 4} = {1, 3}
EnumEqDiff        == {1, 3} = (1..4) \ {2, 4}
DiffNested        == Cardinality({(1..4) \ {2, 4}, {1, 3}}) = 1
DiffSameEmpty     == (1..4) \ (1..4) = {}
DiffSameNested    == Cardinality({(1..4) \ (1..4), {}}) = 1
PredTwo           == {x \in 1..2 : TRUE}
LazyDiffEqEnum    == PredTwo \ {2} = {1}
LazyDiffMember    == 1 \in PredTwo \ {2}
LazyDiffNotMember == 2 \notin PredTwo \ {2}
CardLazyDiff      == Cardinality(PredTwo \ {2}) = 1
FiniteLazyDiff    == IsFiniteSet(PredTwo \ {2})
FPLazyDiffEnum    == Fingerprint(PredTwo \ {2}) = Fingerprint({1})

-----------------------------------------------------------------------------
\* SetCupValue. PredTwo as the left operand keeps this as a lazy union.

CupEqEnum        == (1..2) \cup {2, 3} = {1, 2, 3}
EnumEqCup        == {1, 2, 3} = (1..2) \cup {2, 3}
CupNested        == Cardinality({(1..2) \cup {2, 3}, {1, 2, 3}}) = 1
CupSym           == (1..2) \cup {2, 3} = {2, 3} \cup (1..2)
CupSymNested     == Cardinality({(1..2) \cup {2, 3}, {2, 3} \cup (1..2)}) = 1
LazyCupEqEnum    == PredTwo \cup {2, 3} = {1, 2, 3}
LazyCupMember    == 3 \in PredTwo \cup {2, 3}
LazyCupNotMember == 4 \notin PredTwo \cup {2, 3}
CardLazyCup      == Cardinality(PredTwo \cup {2, 3}) = 3
FiniteLazyCup    == IsFiniteSet(PredTwo \cup {2, 3})
FPLazyCupEnum    == Fingerprint(PredTwo \cup {2, 3}) = Fingerprint({1, 2, 3})

-----------------------------------------------------------------------------
\* UnionValue.

UnionPower       == UNION (SUBSET {1, 2}) = {1, 2}
UnionPowerRev    == {1, 2} = UNION (SUBSET {1, 2})
UnionPowerNested == Cardinality({UNION (SUBSET {1, 2}), {1, 2}}) = 1
UnionDuplicate   == UNION {{1, 2}, {2, 3}} = {1, 2, 3}
UnionMember      == 2 \in UNION (SUBSET {1, 2})
UnionNotMember   == 3 \notin UNION (SUBSET {1, 2})
CardUnion        == Cardinality(UNION (SUBSET {1, 2})) = 2
FiniteUnion      == IsFiniteSet(UNION (SUBSET {1, 2}))
FPUnionEnum      == Fingerprint(UNION (SUBSET {1, 2})) = Fingerprint({1, 2})

-----------------------------------------------------------------------------
\* SetPredValue.

PredEqEnum    == {x \in 1..4 : x % 2 = 0} = {2, 4}
EnumEqPred    == {2, 4} = {x \in 1..4 : x % 2 = 0}
PredNested    == Cardinality({{x \in 1..4 : x % 2 = 0}, {2, 4}}) = 1
PredAll       == {x \in 1..4 : TRUE} = 1..4
PredAllNested == Cardinality({{x \in 1..4 : TRUE}, 1..4}) = 1
PredMember    == 2 \in {x \in 1..4 : x % 2 = 0}
PredNotMember == 3 \notin {x \in 1..4 : x % 2 = 0}
CardPred      == Cardinality({x \in 1..4 : x % 2 = 0}) = 2
FinitePred    == IsFiniteSet({x \in 1..4 : x % 2 = 0})
FPPredEnum    == Fingerprint({x \in 1..4 : x % 2 = 0}) = Fingerprint({2, 4})

-----------------------------------------------------------------------------
\* FcnLambdaValue, FcnRcdValue, RecordValue, and TupleValue.

F == [x \in {"a", "b"} |-> IF x = "a" THEN 1 ELSE 2]
R == [a |-> 1, b |-> 2]
T == <<1, 2>>

FcnEqRecord           == F = R
RecordEqFcn           == R = F
FcnRecordNested       == Cardinality({F, R}) = 1
FcnEqTuple            == [x \in 1..2 |-> x] = T
TupleEqFcn            == T = [x \in 1..2 |-> x]
FcnTupleNested        == Cardinality({[x \in 1..2 |-> x], T}) = 1
RecordEqTupleFunction == [a |-> 1] = [x \in {"a"} |-> 1]
FcnDomain             == DOMAIN F = {"a", "b"}
FcnApply              == F["a"] = 1
RecordDomain          == DOMAIN R = {"a", "b"}
RecordApply           == R["b"] = 2
TupleDomain           == DOMAIN T = 1..2
TupleApply            == T[2] = 2
FPFcnRecord           == Fingerprint(F) = Fingerprint(R)
FPFcnTuple            == Fingerprint([x \in 1..2 |-> x]) = Fingerprint(T)

\* LET-bound expressions exercise LazyValue evaluation and caching.
LazySetEquality    == LET S == {1, 2} IN S = {2, 1}
LazySetNested      ==
  LET S == {1, 2} IN Cardinality({S, {2, 1}}) = 1
LazyFcnApplication ==
  LET G == [x \in 1..2 |-> x + 1] IN G[2] = 3

FcnExceptSame      == [F EXCEPT !["a"] = 1] = F
FcnExceptUpdate    == [F EXCEPT !["a"] = 3] = [a |-> 3, b |-> 2]
TupleExceptSame    == [T EXCEPT ![1] = 1] = T
TupleExceptUpdate  == [T EXCEPT ![2] = 3] = <<1, 3>>
RecordExceptSame   == [R EXCEPT !.a = 1] = R
RecordExceptUpdate == [R EXCEPT !.b = 3] = [a |-> 1, b |-> 3]
FPFcnExceptSame    == Fingerprint([F EXCEPT !["a"] = 1]) = Fingerprint(F)
FPTupleExceptSame  == Fingerprint([T EXCEPT ![1] = 1]) = Fingerprint(T)
FPRecordExceptSame == Fingerprint([R EXCEPT !.a = 1]) = Fingerprint(R)

\* EXCEPT edge paths: missing domain points are no-ops, nested paths update only the selected component, and @ denotes the value before that update.
FcnExceptMissing    == [F EXCEPT !["c"] = 9] = F
TupleExceptMissing  == [T EXCEPT ![3] = 9] = T
RecordExceptMissing == [R EXCEPT !.c = 9] = R
NestedFcn           == [i \in 1..2 |-> [j \in 1..2 |-> 10 * i + j]]
NestedFcnExcept     == [NestedFcn EXCEPT ![1][2] = 99] = [i \in 1..2 |-> [j \in 1..2 |-> IF i = 1 /\ j = 2 THEN 99 ELSE 10 * i + j]]
NestedTupleExcept   == [<<1, <<2, 3>>>> EXCEPT ![2][1] = 9] = <<1, <<9, 3>>>>
NestedRecordExcept  == [[a |-> [b |-> 1]] EXCEPT !.a.b = 2] = [a |-> [b |-> 2]]
FcnExceptAt         == [F EXCEPT !["a"] = @ + 1] = [a |-> 2, b |-> 2]
TupleExceptAt       == [T EXCEPT ![2] = @ + 1] = <<1, 3>>
RecordExceptAt      == [R EXCEPT !.b = @ + 1] = [a |-> 1, b |-> 3]
NestedExceptMissing == [NestedFcn EXCEPT ![1][3] = 99] = NestedFcn
FcnExceptLastWins   == [F EXCEPT !["a"] = 9, !["a"] = 1] = F
\* Multiple EXCEPT clauses are successive updates, so @ in a later clause denotes the value after the preceding updates, not the original.
FcnExceptAtNested   == [F EXCEPT !["a"] = 9, !["a"] = @ + 1] = [a |-> 10, b |-> 2]
TupleExceptLastWins == [T EXCEPT ![2] = 9, ![2] = 2] = T

\* Combine merges two functions and prefers the left operand on the shared domain.
FcnCombineDisjoint == Combine([x \in {1} |-> 0], [x \in {2} |-> 1]) = [x \in {1, 2} |-> IF x = 1 THEN 0 ELSE 1]
FcnCombineLeftWins == Combine([x \in {1} |-> 0], [x \in {1} |-> 1]) = [x \in {1} |-> 0]
IntervalFcnCombine == Combine([x \in 1..1 |-> 0], [x \in {1} |-> 1]) = [x \in {1} |-> 0]

IntervalEmptySubsetEmpty == 2..1 \subseteq 5..4
IntervalEmptySubsetEnum  == 2..1 \subseteq {}
IntervalEmptySubsetNat   == 2..1 \subseteq Nat
IntervalNotSubsetEmpty   == ~(1..3 \subseteq 2..1)
EmptyIntervalsNested     == Cardinality({2..1, 5..4, {}}) = 1
FPEmptyIntervals         == Fingerprint(2..1) = Fingerprint({})

\* Empty functions have the same empty domain regardless of how that domain is represented; the empty tuple is that unique function.
EmptyIntervalFcnEqTuple == [x \in 2..1 |-> x] = <<>>
EmptyEnumFcnEqTuple     == [x \in {} |-> x] = <<>>
EmptyTupleEqIntervalFcn == <<>> = [x \in 2..1 |-> x]
EmptyIntervalFcnsEq     == [x \in 2..1 |-> x] = [x \in 3..2 |-> x]
EmptyIntervalFcnsNested == Cardinality({[x \in 2..1 |-> x], [x \in 3..2 |-> x]}) = 1
EmptyIntervalFcnsSetEq  == {[x \in 2..1 |-> x], [x \in 3..2 |-> x]} = {[x \in 2..1 |-> x]}
\* Reversing equality invokes FcnLambdaValue.toTuple on the empty interval 1..(-1).
NegativeEmptyIntervalFcnEqTuple          == [x \in 1..(-1) |-> x] = <<>>
EmptyTupleEqNegativeIntervalFcn(ignored) == <<>> = [x \in 1..(-1) |-> x]
EmptyIntervalFcnNested                   == Cardinality({[x \in 2..1 |-> x], <<>>}) = 1
EmptyEnumFcnNested                       == Cardinality({[x \in {} |-> x], <<>>}) = 1
EmptyFcnDomainsNested                    == Cardinality({[x \in 2..1 |-> x], [x \in {} |-> x]}) = 1
EmptyFcnNested                           == Cardinality({[x \in 2..1 |-> x], [x \in {} |-> x], <<>>}) = 1
EmptyFcnSetEqSingleton                   == {[x \in 2..1 |-> x], [x \in {} |-> x], <<>>} = {<<>>}
EmptyFcnSetPermutation                   == {[x \in 2..1 |-> x], [x \in {} |-> x], <<>>} = {<<>>, [x \in {} |-> x], [x \in 2..1 |-> x]}
ChooseEmptyFcnSet                        == (CHOOSE f \in {[x \in 2..1 |-> x], [x \in {} |-> x], <<>>} : TRUE) = <<>>
FPEmptyFcnTuple                          == Fingerprint([x \in 2..1 |-> x]) = Fingerprint(<<>>)
FPMixedEmptyFcnSet                       == Fingerprint({[x \in 2..1 |-> x], <<>>}) = Fingerprint({<<>>})
CardSubsetMixedEmptyFcn                  == Cardinality(SUBSET {[x \in 2..1 |-> x], <<>>}) = 2
SubsetMixedEmptyFcnEq                    == SUBSET {[x \in 2..1 |-> x], <<>>} = {{}, {<<>>}}
CardCupMixedEmptyFcn                     == Cardinality({[x \in 2..1 |-> x]} \cup {<<>>}) = 1
CardUnionMixedEmptyFcn                   == Cardinality(UNION {{[x \in 2..1 |-> x]}, {<<>>}}) = 1
CardFcnSetMixedEmptyFcn                  == Cardinality([{[x \in 2..1 |-> x], <<>>} -> {0, 1}]) = 2
CardRcdSetMixedEmptyFcn                  == Cardinality([a : {[x \in 2..1 |-> x], <<>>}]) = 1
CardTupleSetMixedEmptyFcn                == Cardinality({[x \in 2..1 |-> x], <<>>} \X {0}) = 1

\* The empty function is unique even when the empty interval bounds and the body differ.
EmptyIntervalBodiesEq         == [x \in 2..1 |-> 1] = [x \in 5..4 |-> 99]
EmptyZeroIntervalFcnEqTuple   == [x \in 0..(-1) |-> x] = <<>>
EmptyCanonicalVsOtherInterval == [x \in 1..0 |-> x] = [x \in 2..1 |-> x]
EmptyIntervalBodiesNested     == Cardinality({[x \in 2..1 |-> 1], [x \in 5..4 |-> 99]}) = 1
EmptyCanonicalVsOtherNested   == Cardinality({[x \in 1..0 |-> x], [x \in 2..1 |-> x]}) = 1
EmptyFcnSingletonEq           == {[x \in 2..1 |-> x]} = {<<>>}
EmptyFcnDomainEq              == DOMAIN [x \in 2..1 |-> x] = DOMAIN <<>>
EmptyFcnExceptNoop            == [[x \in 2..1 |-> x] EXCEPT ![1] = 9] = <<>>
\* The empty function remains unique when it is only a component of another value.
NestedEmptyFcnEq        == [i \in {1} |-> [x \in 2..1 |-> x]] = [i \in {1} |-> <<>>]
NestedEmptyFcnNested    == Cardinality({[i \in {1} |-> [x \in 2..1 |-> x]], [i \in {1} |-> <<>>]}) = 1
NestedEmptyRecordEq     == [a |-> [x \in 2..1 |-> x]] = [a |-> <<>>]
NestedEmptyRecordNested == Cardinality({[a |-> [x \in 2..1 |-> x]], [a |-> <<>>]}) = 1
NestedEmptyTupleEq      == <<[x \in 2..1 |-> x]>> = <<<<>>>>
NestedEmptyTupleNested  == Cardinality({<<[x \in 2..1 |-> x]>>, <<<<>>>>}) = 1
FPEmptyIntervalFcns     == Fingerprint([x \in 2..1 |-> x]) = Fingerprint([x \in 3..2 |-> x])
\* The empty function is the empty sequence, so the Sequences operators accept it.
LenEmptyEnumFcn         == Len([x \in {} |-> x]) = 0
LenCanonicalEmptyFcn    == Len([x \in 1..0 |-> x]) = 0
AppendCanonicalEmptyFcn == Append([x \in 1..0 |-> x], 1) = <<1>>
EmptyEnumFcnInSeqEmpty  == [x \in {} |-> x] \in Seq({})

-----------------------------------------------------------------------------
\* SetOfFcnsValue.

FcnSetEqEnum                == [{"a"} -> {1, 2}] = {[a |-> 1], [a |-> 2]}
FcnSetEqEnumRev             == {[a |-> 1], [a |-> 2]} = [{"a"} -> {1, 2}]
FcnSetNested                == Cardinality({[{"a"} -> {1, 2}], {[a |-> 1], [a |-> 2]}}) = 1
FcnSetMember                == [a |-> 1] \in [{"a"} -> {1, 2}]
FcnSetNotMember             == [a |-> 3] \notin [{"a"} -> {1, 2}]
CardFcnSet                  == Cardinality([{"a"} -> {1, 2}]) = 2
FiniteFcnSet                == IsFiniteSet([{"a"} -> {1, 2}])
FPFcnSetEnum                == Fingerprint([{"a"} -> {1, 2}]) = Fingerprint({[a |-> 1], [a |-> 2]})
EmptyDomainFcnSetEq         == [{} -> Nat] = [{} -> Int]
EmptyDomainFcnSetSingleton  == [{} -> Nat] = {<<>>}
EmptyIntervalDomainFcnSetEq == [2..1 -> {1, 2}] = [{} -> {3}]
CardSingletonRangeNat       == Cardinality([Nat -> {0}]) = 1
FiniteSingletonRangeNat     == IsFiniteSet([Nat -> {0}])
EmptyFcnInEmptyDomainSet    == [x \in 2..1 |-> x] \in [{} -> {1}]
EmptyRangeNatEqEmpty        == [Nat -> {}] = {}
CardEmptyRangeNat           == Cardinality([Nat -> {}]) = 0
FiniteEmptyRangeNat         == IsFiniteSet([Nat -> {}])
EmptyRangeFcnSetSingleton   == [{} -> {}] = {<<>>}
EmptyFcnInEmptyRangeSet     == <<>> \in [{} -> {}]
NatZeroFcnApply             == [x \in Nat |-> 0][0] = 0
NatZeroFcnDomain            == DOMAIN [x \in Nat |-> 0] = Nat
NatExceptApply              == [[x \in Nat |-> 0] EXCEPT ![0] = 1][0] = 1
NatExceptOrig               == [[x \in Nat |-> 0] EXCEPT ![0] = 1][1] = 0
NatExceptAt                 == [[x \in Nat |-> 0] EXCEPT ![0] = @ + 1][0] = 1
NatExceptDomain             == DOMAIN [[x \in Nat |-> 0] EXCEPT ![0] = 1] = Nat
BoolZeroFcnMember           == [x \in BOOLEAN |-> 0] \in [BOOLEAN -> {0}]
BoolZeroFcnForall           == \A f \in [BOOLEAN -> {0}] : f[TRUE] = 0
FcnSetBoolSingleton         == [BOOLEAN -> {0}] = {[x \in BOOLEAN |-> 0]}
ChooseBoolFcn               == (CHOOSE f \in [BOOLEAN -> {0}] : TRUE) = [x \in BOOLEAN |-> 0]
CardBoolFcnSet              == Cardinality([BOOLEAN -> {0, 1}]) = 4
StringZeroApply             == [x \in STRING |-> 0][""] = 0
FcnSetNatCupEmpty           == [Nat -> {0}] = [Nat \cup {} -> {0}]
FcnSetRangeCupEmpty         == [Nat -> {0}] = [Nat -> {0} \cup {}]
EmptyRangeSTRING            == [STRING -> {}] = {}
CardEmptyRangeSTRING        == Cardinality([STRING -> {}]) = 0
FiniteEmptyRangeSTRING      == IsFiniteSet([STRING -> {}])
CardSingletonRangeSeqEmpty  == Cardinality([Seq({}) -> {0}]) = 1
FiniteSeqEmptyFcnSet        == IsFiniteSet([Seq({}) -> {1, 2}])

-----------------------------------------------------------------------------
\* SetOfRcdsValue.

RcdSetEqEnum            == [a : {1, 2}] = {[a |-> 1], [a |-> 2]}
RcdSetEqEnumRev         == {[a |-> 1], [a |-> 2]} = [a : {1, 2}]
RcdSetNested            == Cardinality({[a : {1, 2}], {[a |-> 1], [a |-> 2]}}) = 1
RcdSetMember            == [a |-> 1] \in [a : {1, 2}]
RcdSetNotMember         == [a |-> 3] \notin [a : {1, 2}]
CardRcdSet              == Cardinality([a : {1, 2}]) = 2
FiniteRcdSet            == IsFiniteSet([a : {1, 2}])
FPRcdSetEnum            == Fingerprint([a : {1, 2}]) = Fingerprint({[a |-> 1], [a |-> 2]})
EmptyRcdFieldEqEmpty    == [a : {}] = {}
EmptyRcdFieldNatEqEmpty == [a : Nat, b : {}] = {}
FiniteEmptyRcdFieldNat  == IsFiniteSet([a : Nat, b : {}])
RcdSetNatCupEmpty       == [a : Nat] = [a : Nat \cup {}]
FiniteSeqEmptyRcdSet    == IsFiniteSet([a : Seq({})])
RcdNatMember            == [a |-> 1] \in [a : Nat]
RcdSetBoolEq            == [a : BOOLEAN] = {[a |-> TRUE], [a |-> FALSE]}
RcdSetBoolMember        == [a |-> TRUE] \in [a : BOOLEAN]
CardRcdSetBool          == Cardinality([a : BOOLEAN]) = 2
FiniteRcdSetBool        == IsFiniteSet([a : BOOLEAN])
RcdSetBoolFieldEq       == [a : BOOLEAN] = [a : {TRUE, FALSE}]

-----------------------------------------------------------------------------
\* SetOfTuplesValue.

TupleSetEqEnum         == ({1, 2} \X {3}) = {<<1, 3>>, <<2, 3>>}
TupleSetEqEnumRev      == {<<1, 3>>, <<2, 3>>} = ({1, 2} \X {3})
TupleSetNested         == Cardinality({({1, 2} \X {3}), {<<1, 3>>, <<2, 3>>}}) = 1
TupleSetMember         == <<1, 3>> \in ({1, 2} \X {3})
TupleSetNotMember      == <<3, 3>> \notin ({1, 2} \X {3})
CardTupleSet           == Cardinality({1, 2} \X {3}) = 2
FiniteTupleSet         == IsFiniteSet({1, 2} \X {3})
FPTupleSetEnum         == Fingerprint({1, 2} \X {3}) = Fingerprint({<<1, 3>>, <<2, 3>>})
TupleSetEqFcnSet       == ({1, 2} \X {1, 2}) = [1..2 -> {1, 2}]
EmptyProductEq         == ({1} \X {}) = (Nat \X {})
EmptyProductEmpty      == (Nat \X {}) = {}
FiniteEmptyProduct     == IsFiniteSet(Nat \X {})
CardEmptyProduct       == Cardinality(Nat \X {}) = 0
EmptyProductIn         == <<1>> \notin (Nat \X {})
NestedProductNeqNary   == (({1} \X {2}) \X {3}) # ({1} \X {2} \X {3})
NaryProductMember      == <<1, 2, 3>> \in ({1} \X {2} \X {3})
NestedProductNotInNary == <<<<1, 2>>, 3>> \notin ({1} \X {2} \X {3})
NaryProductEqEnum      == ({1} \X {2} \X {3}) = {<<1, 2, 3>>}
FiniteSeqEmptyProduct  == IsFiniteSet(Seq({}) \X {1})
TupleInSeq             == <<1, 2>> \in Seq({1, 2})
FcnInSeq               == [x \in 1..2 |-> x] \in Seq({1, 2})

-----------------------------------------------------------------------------
\* UserValue implementations supplied by Integers, Strings, and Sequences. Nat is already exercised as the non-enumerated operand of CapEqEnum.

IntCapEnum                 == Int \cap {-1, 0, 1} = {-1, 0, 1}
StringCapEnum              == STRING \cap {"a", "b"} = {"a", "b"}
SeqCapEnum                 == Seq({1}) \cap {<<>>, <<1>>, <<1, 1>>, <<2>>} = {<<>>, <<1>>, <<1, 1>>}
FPIntCapEnum               == Fingerprint(Int \cap {-1, 0, 1}) = Fingerprint({-1, 0, 1})
FPStringCapEnum            == Fingerprint(STRING \cap {"a", "b"}) = Fingerprint({"a", "b"})
FPSeqCapEnum               == Fingerprint(Seq({1}) \cap {<<>>, <<1>>, <<1, 1>>, <<2>>}) = Fingerprint({<<>>, <<1>>, <<1, 1>>})
EmptySeqInSeqEmpty         == <<>> \in Seq({})
FiniteSeqEmpty             == IsFiniteSet(Seq({}))
EnumSubsetSeqEmpty         == {<<>>} \subseteq Seq({})
SeqCapEmptyEnum            == Seq({}) \cap {<<>>} = {<<>>}
SeqCupEmpty                == Seq({}) \cup {} = Seq({})
EmptyInUnionSeq            == <<>> \in UNION {Seq({})}
EmptyInSubsetSeq           == {} \in SUBSET Seq({})
SingletonInSubsetSeq       == {<<>>} \in SUBSET Seq({})
FiniteSubsetSeqEmpty       == IsFiniteSet(SUBSET Seq({}))
EmptyStringInSTRING        == "" \in STRING
EnumSubsetNat              == {1} \subseteq Nat
EnumSubsetInt              == {1} \subseteq Int
NatCupEmptyEqNat           == Nat \cup {} = Nat
NatPairCupEmpty            == Cardinality({Nat, Nat \cup {}}) = 1
ZeroInNatCupZero           == 0 \in (Nat \cup {0})
EnumSubsetNatCupZero       == {0} \subseteq (Nat \cup {0})
OneInNatDiffZero           == 1 \in Nat \ {0}
ZeroNotInNatDiffZero       == 0 \notin Nat \ {0}
EnumSubsetNatDiff          == {1} \subseteq Nat \ {0}
ZeroInPredNat              == 0 \in {x \in Nat : TRUE}
BoolMember                 == TRUE \in BOOLEAN
BoolEqEnum                 == BOOLEAN = {TRUE, FALSE}
CardBool                   == Cardinality(BOOLEAN) = 2
FiniteBool                 == IsFiniteSet(BOOLEAN)
ChooseBool                 == (CHOOSE x \in BOOLEAN : x) = TRUE
BoolSubsetEnum             == BOOLEAN \subseteq {TRUE, FALSE}
EnumSubsetBool             == {TRUE, FALSE} \subseteq BOOLEAN
BoolPredTrue               == {x \in BOOLEAN : x} = {TRUE}
CardBoolPredTrue           == Cardinality({x \in BOOLEAN : x}) = 1
SubsetBoolEq               == SUBSET BOOLEAN = {{}, {TRUE}, {FALSE}, {TRUE, FALSE}}
CardSubsetBool             == Cardinality(SUBSET BOOLEAN) = 4
FPBoolEnum                 == Fingerprint(BOOLEAN) = Fingerprint({TRUE, FALSE})
EmptyInSeqOne              == <<>> \in Seq({1})
EnumSubsetSeqOne           == {<<1>>} \subseteq Seq({1, 2})
EmptyInSeqCap              == <<>> \in (Seq({}) \cap Seq({1}))
FiniteSeqCapEmptyOne       == IsFiniteSet(Seq({}) \cap Seq({1}))
ZeroInNatCapNat            == 0 \in Nat \cap Nat
EmptyInStringCap           == "" \in STRING \cap STRING
PairInNatProduct           == <<0, 1>> \in (Nat \X {1})
EnumSubsetNatProduct       == {<<0, 1>>} \subseteq (Nat \X {1})
CaseTrue                   == (CASE TRUE -> 1 [] OTHER -> 2) = 1
CaseOther                  == (CASE FALSE -> 1 [] OTHER -> 2) = 2
BoolPredFalse              == {x \in BOOLEAN : ~x} = {FALSE}
BoolIdApply                == [x \in BOOLEAN |-> x][TRUE] = TRUE
RcdDomain                  == DOMAIN [a |-> 1] = {"a"}
RcdExcept                  == [[a |-> 0] EXCEPT !.a = 1] = [a |-> 1]
TupleInSeqNat              == <<1>> \in Seq(Nat)
OneInIntCapNat             == 1 \in Int \cap Nat
EnumInSubsetNat            == {1} \in SUBSET Nat
LenTuple                   == Len(<<1, 2>>) = 2
SubsetSingleton            == SUBSET {TRUE} = {{}, {TRUE}}
EmptyNeqString             == "" # "a"
ChooseSingleton            == (CHOOSE x \in {1} : TRUE) = 1
EmptyInSeqCapDisjoint      == <<>> \in (Seq({1}) \cap Seq({2}))
BoolCupTrue                == BOOLEAN \cup {TRUE} = BOOLEAN
TrueCupBool                == {TRUE} \cup BOOLEAN = BOOLEAN
UnionBool                  == UNION {BOOLEAN} = BOOLEAN
BoolSubsetSelf             == BOOLEAN \subseteq BOOLEAN
FourInBoundedPred          == 4 \in {x \in Nat : x < 5}
FiveNotInBoundedPred       == 5 \notin {x \in Nat : x < 5}
EnumSubsetBoundedPred      == {0, 1, 2, 3, 4} \subseteq {x \in Nat : x < 5}
ZeroNotInNatDiffNat        == 0 \notin Nat \ Nat
FiniteEnumDiffNat          == IsFiniteSet((1..10) \ Nat)
EnumDiffNatEmpty           == (1..10) \ Nat = {}
ThreeInIntervalCapNat      == 3 \in (1..5) \cap Nat
FiniteIntervalCapNat       == IsFiniteSet((1..5) \cap Nat)
IntervalCapNatEq           == (1..5) \cap Nat = 1..5
FinitePredOverEnum         == IsFiniteSet({x \in 1..10 : x \in Nat})
PredOverEnumEq             == {x \in 1..10 : x \in Nat} = 1..10
CardStringSingletonRange   == Cardinality([STRING -> {0}]) = 1
FiniteStringSingletonRange == IsFiniteSet([STRING -> {0}])
FcnDomainOrder             == [i \in {"b", "a"} |-> 1] = [a |-> 1, b |-> 1]
NestedRcdExcept            == [[a |-> [b |-> 1]] EXCEPT !.a.b = 2] = [a |-> [b |-> 2]]
ConcatEmptyRight           == <<1, 2>> \o <<>> = <<1, 2>>
DivPos                     == 5 \div 2 = 2
ModPos                     == 5 % 2 = 1
UnionIntervals             == UNION {1..2, 3..4} = {1, 2, 3, 4}
CardNatIntPair             == Cardinality({Nat, Int}) = 2
NatIntSetPerm              == {Nat, Int} = {Int, Nat}
HeadTuple                  == Head(<<1, 2>>) = 1
TailSingleton              == Tail(<<1>>) = <<>>
AppendEmpty                == Append(<<>>, 1) = <<1>>
ConcatTuples               == <<1>> \o <<2>> = <<1, 2>>
SubSeqEmpty                == SubSeq(<<1, 2, 3>>, 2, 1) = <<>>
LenEmptyTuple              == Len(<<>>) = 0
NegEmptyInterval           == 0..(-1) = {}
CardNegEmptyInterval       == Cardinality(0..(-1)) = 0
LambdaExcept               == [[x \in {1} |-> x] EXCEPT ![1] = 2] = [x \in {1} |-> 2]
DivNegDividend             == (-5) \div 2 = -3
ModNegDividend             == (-5) % 2 = 1
FiniteNatCapEmpty          == IsFiniteSet(Nat \cap {})
FiniteEmptyDiffNat         == IsFiniteSet({} \ Nat)
OneInUnionNat              == 1 \in UNION {Nat}
VacuousForall              == \A x \in {} : FALSE
EmptyExists                == ~(\E x \in {} : TRUE)

-----------------------------------------------------------------------------
\* Same-constructor and lazy-to-lazy comparisons exercise structural paths without relying exclusively on an explicit SetEnumValue as the other side.

RecordPermutation == [a |-> 1, b |-> 2] = [b |-> 2, a |-> 1]
TupleReflexive    == <<1, 2>> = <<1, 2>>
TupleDomainDiffer == <<1, 2>> # [x \in 2..3 |-> x - 1]

IntervalReflexive   == 1..3 = 1..3
IntervalDiffer      == 1..3 # 1..4
SubsetIntervalEq    == SUBSET (1..3) = SUBSET {1, 2, 3}
SubsetIntervalEqRev == SUBSET {1, 2, 3} = SUBSET (1..3)

CapLazyEqEnum   == (SUBSET {1, 2}) \cap (SUBSET {2, 3}) = {{}, {2}}
CupLazyEqEnum   == (SUBSET {1}) \cup (SUBSET {2}) = {{}, {1}, {2}}
DiffLazyEqEnum  == (SUBSET {1, 2}) \ (SUBSET {2}) = {{1}, {1, 2}}
UnionLazyEqEnum == UNION {SUBSET {1}, SUBSET {2}} = {{}, {1}, {2}}
PredEquivalent  == {x \in 1..4 : x % 2 = 0} = {x \in 1..4 : x = 2 \/ x = 4}

FcnSetStructuralEq   == [1..2 -> {1}] = [{1, 2} -> {1}]
FcnSetStructuralDiff == [1..2 -> {1}] # [1..2 -> {2}]
RcdSetPermutation    == [a : {1}, b : {2}] = [b : {2}, a : {1}]
TupleSetStructuralEq == (1..2) \X {3} = {1, 2} \X {3}

NatDiffInt        == Nat # Int
IntDiffNat        == Int # Nat
StringInStringSet == "a" \in STRING

-----------------------------------------------------------------------------
\* Bounded quantification and unique-witness CHOOSE over Enumerable Values.

EnumQuantifiers     ==
  /\ \E x \in {1} : x = 1
  /\ \A x \in {1} : x = 1
  /\ (CHOOSE x \in {1} : TRUE) = 1
IntervalQuantifiers ==
  /\ \E x \in 1..1 : x = 1
  /\ \A x \in 1..1 : x = 1
  /\ (CHOOSE x \in 1..1 : TRUE) = 1
SubsetQuantifiers   ==
  /\ \E s \in SUBSET {} : s = {}
  /\ \A s \in SUBSET {} : s = {}
  /\ (CHOOSE s \in SUBSET {} : TRUE) = {}
CapQuantifiers      ==
  LET S == Nat \cap {x \in {1} : TRUE}
  IN  /\ \E x \in S : x = 1
      /\ \A x \in S : x = 1
      /\ (CHOOSE x \in S : TRUE) = 1
DiffQuantifiers     ==
  LET S == {x \in {1} : TRUE} \ {}
  IN  /\ \E x \in S : x = 1
      /\ \A x \in S : x = 1
      /\ (CHOOSE x \in S : TRUE) = 1
CupQuantifiers      ==
  LET S == {x \in {1} : TRUE} \cup {x \in {} : TRUE}
  IN  /\ \E x \in S : x = 1
      /\ \A x \in S : x = 1
      /\ (CHOOSE x \in S : TRUE) = 1
UnionQuantifiers    ==
  LET S == UNION {{x \in {1} : TRUE}}
  IN  /\ \E x \in S : x = 1
      /\ \A x \in S : x = 1
      /\ (CHOOSE x \in S : TRUE) = 1
PredQuantifiers     ==
  LET S == {x \in {1} : TRUE}
  IN  /\ \E x \in S : x = 1
      /\ \A x \in S : x = 1
      /\ (CHOOSE x \in S : TRUE) = 1
FcnSetQuantifiers   ==
  LET S == [{} -> {1}]
  IN  /\ \E f \in S : f = <<>>
      /\ \A f \in S : f = <<>>
      /\ (CHOOSE f \in S : TRUE) = <<>>
RcdSetQuantifiers   ==
  LET S == [a : {1}]
  IN  /\ \E r \in S : r = [a |-> 1]
      /\ \A r \in S : r = [a |-> 1]
      /\ (CHOOSE r \in S : TRUE) = [a |-> 1]
TupleSetQuantifiers ==
  LET S == {1} \X {2}
  IN  /\ \E t \in S : t = <<1, 2>>
      /\ \A t \in S : t = <<1, 2>>
      /\ (CHOOSE t \in S : TRUE) = <<1, 2>>

\* CHOOSE must be extensional: equivalent set representations denote the same predicate and therefore have the same chosen value, even with many
\* witnesses.
ChooseIntervalEnum == (CHOOSE x \in 1..3 : TRUE) = (CHOOSE x \in {3, 2, 1} : TRUE)
ChooseSubsetEnum   == (CHOOSE s \in SUBSET {1, 2} : TRUE) = (CHOOSE s \in {{1, 2}, {2}, {1}, {}} : TRUE)
ChooseCapEnum      == (CHOOSE x \in Nat \cap {1, 2} : TRUE) = (CHOOSE x \in {2, 1} : TRUE)
ChooseDiffEnum     == (CHOOSE x \in (1..4) \ {2, 4} : TRUE) = (CHOOSE x \in {3, 1} : TRUE)
ChooseCupEnum      == (CHOOSE x \in PredTwo \cup {2, 3} : TRUE) = (CHOOSE x \in {3, 2, 1} : TRUE)
ChooseUnionEnum    == (CHOOSE x \in UNION (SUBSET {1, 2}) : TRUE) = (CHOOSE x \in {2, 1} : TRUE)
ChoosePredEnum     == (CHOOSE x \in {y \in 1..4 : y % 2 = 0} : TRUE) = (CHOOSE x \in {4, 2} : TRUE)
ChooseFcnSetEnum   == (CHOOSE f \in [{"a"} -> {1, 2}] : TRUE) = (CHOOSE f \in {[a |-> 2], [a |-> 1]} : TRUE)
ChooseRcdSetEnum   == (CHOOSE r \in [a : {1, 2}] : TRUE) = (CHOOSE r \in {[a |-> 2], [a |-> 1]} : TRUE)
ChooseTupleSetEnum == (CHOOSE t \in ({1, 2} \X {3}) : TRUE) = (CHOOSE t \in {<<2, 3>>, <<1, 3>>} : TRUE)

-----------------------------------------------------------------------------
\* Boundary intervals, empty functions, and operators over infinite sets.

MaxInt      == 2147483647
MinInt      == -2147483647 - 1
MaxInterval == MaxInt..MaxInt

\* The boundary interval MaxInt..MaxInt denotes the singleton {MaxInt}; its set operations and fingerprint agree with that set.
MaxIntervalSubset(ignored) == MaxInterval \subseteq {MaxInt}
MaxIntervalDiff(ignored)   == MaxInterval \ {} = {MaxInt}
MaxIntervalCap(ignored)    == MaxInterval \cap {MaxInt} = {MaxInt}
MaxIntervalCup(ignored)    == MaxInterval \cup {} = {MaxInt}
MaxIntervalPred(ignored)   == {x \in MaxInterval : TRUE} = {MaxInt}
FPMaxInterval(ignored)     == Fingerprint(MaxInterval) = Fingerprint({MaxInt})
MaxIntervalExists          == ~(\E x \in MaxInterval : x = MinInt)
MaxIntervalForall          == \A x \in MaxInterval : x = MaxInt
MaxIntervalChoose          == (CHOOSE x \in MaxInterval : TRUE) = MaxInt

\* Equivalent interval and enumerated-set representations agree under equality, subset, function construction, and application.
MaxIntervalEqEnum             == MaxInterval = {MaxInt}
MaxEnumSubsetInterval         == {MaxInt} \subseteq MaxInterval
MaxIntervalReflexiveSubset    == MaxInterval \subseteq MaxInterval
CardMaxIntervalPair           == Cardinality({MaxInterval, {MaxInt}}) = 1
CardSubsetMaxInterval         == Cardinality(SUBSET MaxInterval) = 2
MaxIntervalFcnApply           == [x \in MaxInt..MaxInt |-> 42][MaxInt] = 42
CardMaxInterval               == Cardinality(MaxInterval) = 1
MaxIntInMaxInterval           == MaxInt \in MaxInterval
MinIntNotInMaxInterval        == MinInt \notin MaxInterval
EmptyInSubsetMax              == {} \in SUBSET MaxInterval
MaxSingletonInSubsetMax       == {MaxInt} \in SUBSET MaxInterval
MinSingletonNotInSubsetMax    == {MinInt} \notin SUBSET MaxInterval
MinIntInSingleton             == MinInt \in MinInt..MinInt
CardMinInterval               == Cardinality(MinInt..MinInt) = 1
MinIntervalEq                 == MinInt..MinInt = {MinInt}
MaxIntervalFcnEq(ignored)     == [x \in MaxInt..MaxInt |-> 0] = [x \in {MaxInt} |-> 0]
MaxIntervalFcnMember(ignored) == [x \in MaxInt..MaxInt |-> 0] \in [{MaxInt} -> {0}]

\* Combine preserves the left operand on the shared boundary domain, whichever operand uses the interval representation.
MaxIntervalFcnCombine(ignored)    == Combine([x \in MaxInt..MaxInt |-> 0], [x \in {MaxInt} |-> 1]) = [x \in {MaxInt} |-> 0]
MaxIntervalFcnCombineRev(ignored) == Combine([x \in {MaxInt} |-> 0], [x \in MaxInt..MaxInt |-> 1]) = [x \in {MaxInt} |-> 0]

\* Values constructed from MaxInterval retain MaxInt as their sole element.
IdentityPred(S)            == {x \in S : TRUE}
MaxPredExists(ignored)     == ~(\E x \in IdentityPred(MaxInterval) : x = MinInt)
MaxPredForall(ignored)     == \A x \in IdentityPred(MaxInterval) : x = MaxInt
MaxCapExists(ignored)      == ~(\E x \in (IdentityPred(MaxInterval) \cap Int) : x = MinInt)
MaxCupExists(ignored)      == ~(\E x \in (IdentityPred(MaxInterval) \cup IdentityPred({})) : x = MinInt)
MaxDiffExists(ignored)     == ~(\E x \in (IdentityPred(MaxInterval) \ {}) : x = MinInt)
MaxUnionExists(ignored)    == ~(\E x \in UNION {IdentityPred(MaxInterval)} : x = MinInt)
MaxTupleSetExists(ignored) == ~(\E t \in (IdentityPred(MaxInterval) \X {0}) : t = <<MinInt, 0>>)
MaxRcdSetExists(ignored)   == ~(\E r \in [a : IdentityPred(MaxInterval)] : r = [a |-> MinInt])
MaxFcnSetExists(ignored)   == ~(\E f \in [{0} -> IdentityPred(MaxInterval)] : f = [x \in {0} |-> MinInt])

\* Empty results over an infinite carrier are finite and extensionally empty.
InfiniteCapEmpty(ignored)             == Nat \cap {} = {}
InfiniteDiffEmpty(ignored)            == Nat \ Nat = {}
InfinitePredEmpty(ignored)            == {x \in Nat : FALSE} = {}
FiniteInfinitePredEmpty(ignored)      == IsFiniteSet({x \in Nat : FALSE})
FiniteCupInfinitePredEmpty(ignored)   == IsFiniteSet({1} \cup {x \in Nat : FALSE})
FiniteUnionInfinitePredEmpty(ignored) == IsFiniteSet(UNION {{x \in Nat : FALSE}})
\* A function whose domain is the mixed empty-function set is the constant function on {<<>>}.
MixedEmptyDomFcn                 == [f \in {[x \in 2..1 |-> x], <<>>} |-> 0]
SingletonEmptyDomFcn             == [f \in {<<>>} |-> 0]
MixedEmptyFcnApplyTuple          == MixedEmptyDomFcn[<<>>] = 0
MixedEmptyFcnApplyInterval       == MixedEmptyDomFcn[[x \in 2..1 |-> x]] = 0
MixedEmptyFcnEq(ignored)         == MixedEmptyDomFcn = SingletonEmptyDomFcn
MixedEmptyFcnDomainEq(ignored)   == DOMAIN MixedEmptyDomFcn = {<<>>}
MixedEmptyFcnDomainCard(ignored) == Cardinality(DOMAIN MixedEmptyDomFcn) = 1
\* The empty function is the empty sequence regardless of which empty interval denotes its domain.
LenEmptyIntervalFcn(ignored)        == Len([x \in 2..1 |-> x]) = 0
AppendEmptyIntervalFcn(ignored)     == Append([x \in 2..1 |-> x], 1) = <<1>>
ConcatEmptyIntervalFcn(ignored)     == [x \in 2..1 |-> x] \o <<1>> = <<1>>
EmptyIntervalFcnInSeqEmpty(ignored) == [x \in 2..1 |-> x] \in Seq({})

\* Seq({}) is the finite singleton {<<>>}.
SeqEmptyEq(ignored)   == Seq({}) = {<<>>}
CardSeqEmpty(ignored) == Cardinality(Seq({})) = 1
\* Subset, quantification, UNION, and derived cardinalities respect that singleton.
SeqEmptySubsetSelf(ignored)  == Seq({}) \subseteq Seq({})
SeqEmptySubsetEnum(ignored)  == Seq({}) \subseteq {<<>>}
SeqEmptyExists(ignored)      == \E s \in Seq({}) : s = <<>>
UnionSeqEmpty(ignored)       == UNION {Seq({})} = {<<>>}
CardSeqEmptyProduct(ignored) == Cardinality(Seq({}) \X {1}) = 1
CardSeqEmptyFcnSet(ignored)  == Cardinality([Seq({}) -> {1, 2}]) = 2
CardSeqEmptyRcdSet(ignored)  == Cardinality([a : Seq({})]) = 1
CardSubsetSeqEmpty(ignored)  == Cardinality(SUBSET Seq({})) = 2
\* Adding an existing element to Nat, or retaining every element of Nat, yields Nat.
NatCupZeroEqNat(ignored) == Nat \cup {0} = Nat
NatCupZeroRefl(ignored)  == (Nat \cup {0}) = (Nat \cup {0})
PredNatEqNat(ignored)    == {x \in Nat : TRUE} = Nat
NatSubsetNat(ignored)    == Nat \subseteq Nat
NatDiffZeroRefl(ignored) == (Nat \ {0}) = (Nat \ {0})
UnionNatEqNat(ignored)   == UNION {Nat} = Nat
NatPairCupZero(ignored)  == Cardinality({Nat, Nat \cup {0}}) = 1
\* [Nat -> {0}] is the singleton containing the constant-zero function.
NatZeroFcnMember(ignored) == [x \in Nat |-> 0] \in [Nat -> {0}]
NatZeroFcnForall(ignored) == \A f \in [Nat -> {0}] : f[0] = 0
FcnSetNatCupZero(ignored) == [Nat -> {0}] = [Nat \cup {0} -> {0}]
\* EXCEPT updates an infinite-domain function extensionally.
NatExceptExt(ignored) == [[x \in Nat |-> 0] EXCEPT ![0] = 1] = [x \in Nat |-> IF x = 0 THEN 1 ELSE 0]
\* Infinite sets are unequal to finite sets when an element witnesses the difference.
NatNeqSingleton(ignored) == Nat # {1}
EmptyNeqNat(ignored)     == {} # Nat
\* Intersections are determined extensionally, including intersections of infinite sets.
SeqCapEmptyOneEq(ignored)   == Seq({}) \cap Seq({1}) = {<<>>}
NatCapNatEq(ignored)        == Nat \cap Nat = Nat
SeqOneSubsetSeqTwo(ignored) == Seq({1}) \subseteq Seq({1, 2})
\* Seq({1}) \cap Seq({2}) is the finite singleton {<<>>}.
FiniteSeqCapDisjoint(ignored) == IsFiniteSet(Seq({1}) \cap Seq({2}))
SeqCapDisjointEq(ignored)     == Seq({1}) \cap Seq({2}) = {<<>>}
\* Every natural number is an integer.
NatSubsetInt(ignored) == Nat \subseteq Int
\* The intersection of Int and Nat is Nat.
IntCapNatEq(ignored) == Int \cap Nat = Nat
\* STRING contains values other than the empty string.
StringNeqEmpty(ignored) == STRING # {""}
\* A bounded comprehension over Nat is finite and equal to 0..4.
FiniteBoundedPred(ignored) == IsFiniteSet({x \in Nat : x < 5})
CardBoundedPred(ignored)   == Cardinality({x \in Nat : x < 5}) = 5
ExistsBoundedPred(ignored) == \E x \in {x \in Nat : x < 5} : x = 4
BoundedPredEq(ignored)     == {x \in Nat : x < 5} = 0..4
\* Nat \ Nat is empty and therefore finite.
FiniteNatDiffNat(ignored) == IsFiniteSet(Nat \ Nat)
\* [STRING -> {0}] is the singleton containing the constant-zero function.
StringZeroFcnMember(ignored) == [x \in STRING |-> 0] \in [STRING -> {0}]

\* Boundary-separated function domains must still induce a transitive ordering.
\* The old overflowing FcnRcdValue comparisons formed a MinInt < 0 < MaxInt
\* cycle, making normalization depend on the source order.
BoundaryIntervalFcns ==
  {[x \in MinInt..MinInt |-> 0], [x \in 0..0 |-> 0], [x \in MaxInt..MaxInt |-> 0]}
BoundaryMixedFcns ==
  {[x \in {MinInt} |-> 0], [x \in {0} |-> 0], [x \in MaxInt..MaxInt |-> 0]}
BoundaryIntervalFcnSetPermutation ==
  BoundaryIntervalFcns =
  {[x \in MaxInt..MaxInt |-> 0], [x \in 0..0 |-> 0], [x \in MinInt..MinInt |-> 0]}
BoundaryMixedFcnSetPermutation ==
  BoundaryMixedFcns =
  {[x \in MaxInt..MaxInt |-> 0], [x \in {0} |-> 0], [x \in {MinInt} |-> 0]}

\* FcnRcdValue.normalize used to walk past index zero when its insertion sort
\* encountered this source order under the overflowing function comparison.
BoundaryFcnDomainNormalizeWith(a, b, c, d) ==
  DOMAIN Combine(Combine(Combine([f \in {a} |-> 0],
                                 [f \in {b} |-> 0]),
                         [f \in {c} |-> 0]),
                 [f \in {d} |-> 0]) = {a, b, c, d}
BoundaryFcnDomainNormalize ==
  BoundaryFcnDomainNormalizeWith([x \in MinInt..MinInt |-> 0],
                                 [x \in (-1)..(-1) |-> 0],
                                 [x \in 1..1 |-> 0],
                                 [x \in 0..0 |-> 0])

\* Force conversion to FcnRcdValue before application and EXCEPT so that the
\* interval select and update paths, rather than FcnLambdaValue's lazy paths,
\* are exercised at both integer boundaries.
BoundaryFcnSelectOne(f, n) == f = f /\ f[n] = n
BoundaryFcnSelect ==
  /\ BoundaryFcnSelectOne([x \in MinInt..MinInt |-> x], MinInt)
  /\ BoundaryFcnSelectOne([x \in MaxInt..MaxInt |-> x], MaxInt)
BoundaryFcnExceptOne(f, n) ==
  f = f /\ [f EXCEPT ![n] = 1][n] = 1
BoundaryFcnExcept ==
  /\ BoundaryFcnExceptOne([x \in MinInt..MinInt |-> 0], MinInt)
  /\ BoundaryFcnExceptOne([x \in MaxInt..MaxInt |-> 0], MaxInt)

\* More than 32 explicit domain elements selects FcnRcdValue's normalized
\* binary-search path.  The boundary element is appended by Combine.
BoundaryFcnBinarySelectWith(g, max) ==
  DOMAIN g = (1..32) \cup {max} /\ g[max] = 1 /\ g[16] = 0
BoundaryFcnBinarySelect ==
  BoundaryFcnBinarySelectWith(
    Combine([x \in 1..32 |-> 0], [x \in {MaxInt} |-> 1]), MaxInt)

\* Exercise interval-backed fingerprinting at each endpoint.
FPBoundaryFcns ==
  /\ Fingerprint([x \in MinInt..MinInt |-> x]) =
     Fingerprint([x \in {MinInt} |-> x])
  /\ Fingerprint([x \in MaxInt..MaxInt |-> x]) =
     Fingerprint([x \in {MaxInt} |-> x])

=============================================================================
