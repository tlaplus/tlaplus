------------------------- MODULE NormalizationCases --------------------------
\* Shared, assumption-free propositions about values built from a set
\* enumeration whose elements are of different kinds, such as {1, "a"}.
EXTENDS Integers, Sequences

CONSTANTS IsFiniteSet(_), TypedA, TypedB,
          RandomElement(_), ToString(_), Print(_, _), TLCEval(_),
          Assert(_, _), _ :> _, _ @@ _

-----------------------------------------------------------------------------
\* Set enumerations.

MixedMember       == 1 \in {1, "a"}
MixedMemberSecond == "a" \in {1, "a"}
MixedSubseteq     == {1, "a"} \subseteq {1, "a"}
MixedNeqEmpty     == {1, "a"} # {}
EmptyNeqMixed     == {} # {1, "a"}
FiniteMixed       == IsFiniteSet({1, "a"})

TypedMember       == TypedA \in {TypedA, TypedB}
TypedIntMember    == TypedA \in {TypedA, 1}
TypedStringMember == TypedA \in {TypedA, "a"}
IntTypedMember    == 1 \in {1, TypedA}

-----------------------------------------------------------------------------
\* Quantifiers that bind a set enumeration. NormalizationLiveness.tla binds it
\* in a liveness property.

MixedBoundMember == \A S \in {{1, "a"}} : 1 \in S

-----------------------------------------------------------------------------
\* Set operators.

MixedCupEmptyMember == 1 \in {1, "a"} \cup {}
MixedCupMember      == 1 \in {1, "a"} \cup {2}
MixedCapMember      == 1 \in {1, "a"} \cap {1}
MixedDiffMember     == 1 \in {1, "a"} \ {2}
MixedPredMember     == 1 \in {x \in {1, "a"} : TRUE}
UnionMixedMember    == 1 \in UNION {{1}, {"a"}}
UnionMixedSingleton == 1 \in UNION {{1, "a"}}

-----------------------------------------------------------------------------
\* Functions.

MixedFcnApply         == [x \in {1, "a"} |-> x][1] = 1
MixedFcnExcept        == [[x \in {1, "a"} |-> x] EXCEPT ![1] = 2][1] = 2
MixedDomainMember     == 1 \in DOMAIN [x \in {1, "a"} |-> x]
MixedFcnEq            == [x \in {1, "a"} |-> x] = [x \in {1, "a"} |-> x]
FcnRangeMixedNeqEmpty == [x \in {1} |-> {1, "a"}][1] # {}

-----------------------------------------------------------------------------
\* A function and a set comprehension over a lazy set, whose values TLC
\* computes and caches the first time it needs them.

LazyFcnExceptDomain    == DOMAIN [[x \in {1} |-> {1, "a"}] EXCEPT ![1] = 2] = {1}
LazyFcnInTuple         == Len(<<[x \in {1} |-> {1, "a"}]>>) = 1
LazyPredFcnSetNeqEmpty == {f \in [{1} -> {{1, "a"}}] : TRUE} # {}
LazyPredSubsetNeqEmpty == {s \in SUBSET {{1, "a"}} : s # {}} # {}

-----------------------------------------------------------------------------
\* Tuples, sequences, and records with a set enumeration as a component.

TupleApplyMixed == <<1, {1, "a"}>>[1] = 1
HeadMixed       == Head(<<1, {1, "a"}>>) = 1
TailMixed       == Len(Tail(<<1, {1, "a"}>>)) = 1
AppendMixed     == Len(Append(<<>>, {1, "a"})) = 1
ConcatMixed     == Len(<<1>> \o <<{1, "a"}>>) = 2
SubSeqMixed     == Len(SubSeq(<<1, {1, "a"}, 2>>, 1, 2)) = 2
SelectSeqMixed  == Len(SelectSeq(<<1, {1, "a"}>>, LAMBDA e : e = 1)) = 1
RcdFieldMixed   == [f |-> 1, g |-> {1, "a"}].f = 1
RcdDomainMixed  == DOMAIN [f |-> {1, "a"}] = {"f"}

-----------------------------------------------------------------------------
\* Set enumerations of tuples, records, functions, and sets.

TupleEnumMember == <<1>> \in {<<1>>, <<"a">>}
RcdEnumMember   == [f |-> 1] \in {[f |-> 1], [f |-> "a"]}
FcnEnumMember   == [x \in {1} |-> 1] \in {[x \in {1} |-> 1], [x \in {"a"} |-> 1]}
SetEnumMember   == {1} \in {{1}, {"a"}}

-----------------------------------------------------------------------------
\* SUBSET, Seq, Cartesian products, function sets, and record sets.

SubsetMixedMember    == {1} \in SUBSET {1, "a"}
SubsetMixedCupMember == {1} \in SUBSET {1, "a"} \cup {}
SeqMixedMember       == <<1>> \in Seq({1, "a"})
SeqMixedPairMember   == <<1, "a">> \in Seq({1, "a"})
ProductMixedMember   == <<1, 2>> \in {1, "a"} \X {2}
ProductEmptyRight    == <<1, 2>> \notin {1, "a"} \X {}
ProductEmptyLeft     == <<1, 2>> \notin {} \X {1, "a"}
ProductEmptyNonTuple == 1 \notin {1, "a"} \X {}
ProductEmptyEq       == {1, "a"} \X {} = {}
FcnSetMixedMember    == [x \in {1} |-> 1] \in [{1} -> {1, "a"}]
MixedFcnSetMember    == [x \in {1, "a"} |-> 1] \in [{1, "a"} -> {1}]
SubsetFcnSetMember   == [x \in {1} |-> 1] \in [{1} -> SUBSET {1, "a"}]
RcdSetMixedMember    == [f |-> 1] \in [f : {1, "a"}]

-----------------------------------------------------------------------------
\* Operators of the TLC module.

RandomElementMixed == RandomElement({1, "a"}) \in {1, "a"}
ToStringMixed      == ToString({1, "a"}) \in STRING
PrintMixed         == Print({1, "a"}, TRUE)
TLCEvalMixed       == 1 \in TLCEval({1, "a"})
ToStringRcd        == ToString([fld2 |-> 0]) = "[fld2 |-> 0]"
ToStringRcdOrder   == ToString([fld1 |-> 1, fld2 |-> 2]) = "[fld1 |-> 1, fld2 |-> 2]"
ToStringFcnOrder   == ToString(("fld1" :> 0) @@ ("fld2" :> 0)) = "[fld1 |-> 0, fld2 |-> 0]"
AssertRcdOrder     == Assert(FALSE, [fld1 |-> 1, fld2 |-> 2])
AssertFcnOrder     == Assert(FALSE, ("fld1" :> 0) @@ ("fld2" :> 0))
=============================================================================
