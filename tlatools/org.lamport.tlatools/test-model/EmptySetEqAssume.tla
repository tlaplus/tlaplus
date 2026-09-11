-------------------------- MODULE EmptySetEqAssume --------------------------
\* TLC checks every assumption at startup (Tool#checkAssumptions). Each name
\* below is a comparison defined in EmptySetEqCases.tla and proved in
\* EmptySetEqCases_proofs.tla. The AssertError assumptions at the end mostly
\* have no proof, because they state what TLC refuses to answer instead of a
\* TLA+ fact; the ones that do have a proof say so, i.e. they record a
\* limitation.
\*
\* See https://github.com/tlaplus/tlaplus/issues/1407
EXTENDS FiniteSets, Integers, Sequences, TLC, TLCExt, EmptySetEqCases

-----------------------------------------------------------------------------
\* Sets of functions that denote {<<>>}, i.e. the empty domain decides.

ASSUME UnitEmptyRangeEnum
ASSUME UnitEmptyRangeSym
ASSUME UnitSingletonRangeEnum
ASSUME UnitSingletonRangeSym
ASSUME UnitTripleRangeEnum
ASSUME UnitTripleRangeSym
ASSUME UnitNatRangeEnum
ASSUME UnitNatRangeSym

ASSUME UnitIntervalEnum
ASSUME UnitIntervalSym
ASSUME UnitIntervalNatEnum
ASSUME UnitIntervalNatSym

ASSUME UnitCapEnum
ASSUME UnitCapSym
ASSUME UnitCupEnum
ASSUME UnitCupSym
ASSUME UnitDiffEnum
ASSUME UnitDiffSym
ASSUME UnitUnionEmptyEnum
ASSUME UnitUnionEmptySym
ASSUME UnitUnionOfEmptyEnum
ASSUME UnitUnionOfEmptySym
ASSUME UnitFilterEnum
ASSUME UnitFilterSym

ASSUME UnitRcdFieldEnum
ASSUME UnitRcdFieldSym
ASSUME UnitRcdNatFieldEnum
ASSUME UnitRcdNatFieldSym
ASSUME UnitRcdFieldNatSym

ASSUME UnitTupleEnum
ASSUME UnitTupleSym
ASSUME UnitTupleNatFirstEnum
ASSUME UnitTupleNatFirstSym
ASSUME UnitTupleNatSecondSym
ASSUME UnitTupleStrFirstSym

ASSUME UnitFcnSetEnum
ASSUME UnitFcnSetSym
ASSUME UnitFcnSetNestedSym
ASSUME UnitFcnSetNatRangeEnum
ASSUME UnitDiffNestedUnitEnum
ASSUME UnitDiffNestedUnitSym

ASSUME UnitRcdFcnSetSym
ASSUME UnitRcdRcdSym
ASSUME UnitRcdTupleSym
ASSUME UnitTupleFcnSetSym
ASSUME UnitTupleRcdSym
ASSUME UnitTupleTupleSym

-----------------------------------------------------------------------------
\* Sets of functions that are empty, i.e. the empty co-domain decides.

ASSUME EmptySingletonEnum
ASSUME EmptySingletonSym
ASSUME EmptyIntervalEnum
ASSUME EmptyIntervalSym

ASSUME EmptyCapEnum
ASSUME EmptyCapSym
ASSUME EmptyCupEnum
ASSUME EmptyCupSym
ASSUME EmptyDiffEnum
ASSUME EmptyDiffSym
ASSUME EmptyUnionEnum
ASSUME EmptyUnionSym
ASSUME EmptyFilterEnum
ASSUME EmptyFilterSym

ASSUME EmptySubsetEmptyEnum
ASSUME EmptySubsetEmptySym
ASSUME EmptySubsetNatEnum
ASSUME EmptySubsetNatSym

ASSUME EmptyRcdEnum
ASSUME EmptyRcdSym
ASSUME EmptyRcdNatEnum
ASSUME EmptyRcdNatSym

ASSUME EmptyTupleEnum
ASSUME EmptyTupleSym
ASSUME EmptyTupleNatEnum
ASSUME EmptyTupleNatSym

ASSUME EmptyNatEnum
ASSUME EmptyNatSym
ASSUME EmptyIntEnum
ASSUME EmptyIntSym
ASSUME EmptySeqEnum
ASSUME EmptySeqSym
ASSUME EmptyStrSym

ASSUME EmptyRcdRangeSym
ASSUME EmptyTupleRangeSym
ASSUME EmptyRcdFcnSetRangeSym
ASSUME EmptyTupleFcnSetRangeSym
ASSUME EmptyFcnSetRangeSym

ASSUME EmptyFcnSetEnum
ASSUME EmptyFcnSetSym

-----------------------------------------------------------------------------
\* Sets of records that are empty, i.e. a single empty field decides.

ASSUME RcdEmptyFieldEnum
ASSUME RcdEmptyFieldSym
ASSUME RcdEmptyNameSym
ASSUME RcdEmptyArityEnum
ASSUME RcdEmptyAritySym
ASSUME RcdEmptyIntervalEnum
ASSUME RcdEmptyIntervalSym
ASSUME RcdEmptyNatFieldEnum
ASSUME RcdEmptyNatFieldSym
ASSUME RcdEmptyFieldNatSym
ASSUME RcdEmptySeqFieldSym
ASSUME RcdEmptyStrFieldSym

ASSUME RcdEmptyFcnSetSym
ASSUME RcdEmptyRcdSym
ASSUME RcdEmptyTupleSym
ASSUME RcdEmptyThenDiffSym

-----------------------------------------------------------------------------
\* Cartesian products that are empty, i.e. a single empty component decides.

ASSUME TupEmptyComponentEnum
ASSUME TupEmptyComponentSym
ASSUME TupEmptyPositionSym
ASSUME TupEmptyArityEnum
ASSUME TupEmptyAritySym
ASSUME TupEmptyIntervalEnum
ASSUME TupEmptyIntervalSym
ASSUME TupEmptyNatFirstEnum
ASSUME TupEmptyNatFirstSym
ASSUME TupEmptyNatSecondSym
ASSUME TupEmptySeqFirstSym
ASSUME TupEmptyStrFirstSym

ASSUME TupEmptyFcnSetSym
ASSUME TupEmptyRcdSym
ASSUME TupEmptyTupleSym
ASSUME TupEmptyThenDiffSym

-----------------------------------------------------------------------------
\* Two sets of different constructors.

ASSUME FcnSetEqRcdSetEmpty
ASSUME FcnSetEqRcdSetNat
ASSUME FcnSetEqTupleSetEmpty
ASSUME FcnSetEqTupleSetNat
ASSUME RcdSetEqTupleSetEmpty
ASSUME UnitDiffRcdSetEmpty
ASSUME UnitDiffTupleSetEmpty

ASSUME RcdSetIsFcnSet
ASSUME TupleSetIsFcnSet
ASSUME TupleSetIsFcnSet3

-----------------------------------------------------------------------------
\* The comparisons of the sections above with their operands swapped, which
\* is what reaches the equals of a set of functions, of records, and of a
\* Cartesian product with an argument of another kind.

ASSUME UnitEmptyRangeRev
ASSUME UnitSingletonRangeRev
ASSUME EmptySingletonRev
ASSUME EmptyNatRev
ASSUME RcdEmptyFieldRev
ASSUME RcdEmptyArityRev
ASSUME TupEmptyComponentRev
ASSUME TupEmptyArityRev

ASSUME RcdSetEqFcnSetEmptyRev
ASSUME RcdSetEqFcnSetNatRev
ASSUME TupleSetEqFcnSetEmptyRev
ASSUME TupleSetEqRcdSetEmptyRev
ASSUME TupleSetEqRcdSetNatRev
ASSUME RcdSetIsFcnSetRev
ASSUME TupleSetIsFcnSetRev

-----------------------------------------------------------------------------
\* Fingerprinting deep-normalizes and enumerates each lazy set representation.
\* The mixed case also checks that equal elements coalesce during normalization.

ASSUME FPUnitNatRange
ASSUME FPUnitIntervalNatRange
ASSUME FPUnitFcnSetNatRange
ASSUME FPUnitRcdDomain
ASSUME FPEmptyNatDomain
ASSUME FPEmptyFiniteDomain
ASSUME FPRcdEmptyNatField
ASSUME FPRcdEmptyFieldNat
ASSUME FPTupEmptyNatFirst
ASSUME FPTupEmptyNatSecond
ASSUME FPRcdEmptyFcnSet
ASSUME FPTupEmptyFcnSet
ASSUME FPEmptyRcdRange
ASSUME FPEmptyRcdFcnSetRange
ASSUME FPRcdSetIsFcnSet
ASSUME FPTupleSetIsFcnSet
ASSUME FPMixedEmptyConstructors
ASSUME FPMixedUnitEmptyConstructors
ASSUME FPMixedNonEmptyConstructors

-----------------------------------------------------------------------------
\* The cardinality of each set above. The ones TLC refuses are AssertError
\* assumptions of the last section.

ASSUME CardUnitEmptyRange
ASSUME CardUnitTripleRange
ASSUME CardUnitInterval
ASSUME CardUnitCap
ASSUME CardUnitFilter

ASSUME CardUnitRcdField
ASSUME CardUnitTuple
ASSUME CardUnitFcnSet
ASSUME CardUnitFcnSetRange

ASSUME CardEmptySingleton
ASSUME CardEmptyInterval
ASSUME CardEmptySubsetEmpty
ASSUME CardEmptyRcdDomain

ASSUME CardEmptyRcdRange
ASSUME CardEmptyTupleRange
ASSUME CardEmptyFcnSetRange

ASSUME CardRcdEmptyField
ASSUME CardRcdEmptyArity
ASSUME CardRcdEmptyPosition
ASSUME CardRcdEmptyInterval
ASSUME CardRcdEmptyFcnSet
ASSUME CardRcdEmptyRcd
ASSUME CardRcdEmptyTuple

ASSUME CardTupEmptyComponent
ASSUME CardTupEmptyPosition
ASSUME CardTupEmptyArity
ASSUME CardTupEmptyInterval
ASSUME CardTupEmptyFcnSet
ASSUME CardTupEmptyRcd
ASSUME CardTupEmptyTuple

ASSUME CardRcdLargeThenEmpty
ASSUME CardRcdEmptyThenLarge
ASSUME CardTupLargeThenEmpty
ASSUME CardTupEmptyThenLarge
ASSUME CardUnitTupleLarge

ASSUME CardRcdEmptyFieldNat
ASSUME CardRcdEmptyThenDiff
ASSUME CardTupEmptyNatSecond

ASSUME CardRcdEmptyNatField
ASSUME CardTupEmptyNatFirst

ASSUME CardRcdEmptyFcnSetNat
ASSUME CardTupEmptyFcnSetNat

ASSUME CardUnitNatRange
ASSUME CardEmptyNatDomain
ASSUME CardUnitFcnSetNat
ASSUME CardEmptyFcnSetNat
ASSUME CardUnitSubsetRange
ASSUME CardEmptySubsetDomain
ASSUME CardSingletonNatDomain
ASSUME CardSingletonSubset
ASSUME CardSingletonAsDomain
ASSUME CardSingletonSubsetDomain
ASSUME CardSingletonLargeDomain
ASSUME CardSingletonSeqEmptyDomain
ASSUME CardSingletonUnionDomain

ASSUME CardSubsetSingletonFcnSet
ASSUME CardTupSingletonFcnSet
ASSUME CardRcdSingletonFcnSet
ASSUME CardSingletonSubsetAsDomain
ASSUME CardSingletonSubsetAsRange
ASSUME CardUnitLargeRange
ASSUME CardEmptyLargeDomain

-----------------------------------------------------------------------------
\* The finiteness of the same sets.

ASSUME FinUnitEmptyRange
ASSUME FinUnitInterval
ASSUME FinUnitRcdField
ASSUME FinUnitTuple
ASSUME FinUnitFcnSet
ASSUME FinUnitFcnSetRange

ASSUME FinUnitNatRange
ASSUME FinUnitStrRange
ASSUME FinUnitFcnSetNat

ASSUME FinEmptySingleton
ASSUME FinEmptyInterval
ASSUME FinEmptySubsetEmpty
ASSUME FinEmptyRcdRange
ASSUME FinEmptyTupleRange
ASSUME FinEmptyFcnSetRange

ASSUME FinEmptyNatDomain
ASSUME FinEmptySeqDomain
ASSUME FinEmptyDiffDomain
ASSUME FinEmptyFcnSetNat

ASSUME FinRcdEmptyField
ASSUME FinRcdEmptyArity
ASSUME FinRcdEmptyPosition
ASSUME FinRcdEmptyFcnSet
ASSUME FinRcdEmptyRcd
ASSUME FinRcdEmptyTuple

ASSUME FinRcdEmptyFieldNat
ASSUME FinRcdEmptyNatField
ASSUME FinRcdEmptyThenDiff
ASSUME FinRcdDiffThenEmpty
ASSUME FinRcdEmptyFcnSetNat

ASSUME FinTupEmptyComponent
ASSUME FinTupEmptyPosition
ASSUME FinTupEmptyArity
ASSUME FinTupEmptyFcnSet
ASSUME FinTupEmptyRcd
ASSUME FinTupEmptyTuple

ASSUME FinTupEmptyNatSecond
ASSUME FinTupEmptyNatFirst
ASSUME FinTupDiffThenEmpty
ASSUME FinTupEmptyFcnSetNat

ASSUME FinSingletonNatDomain
ASSUME FinSingletonIntDomain
ASSUME FinSingletonStrDomain
ASSUME FinSingletonDiffDomain
ASSUME FinSingletonSeqDomain

ASSUME FinSingletonInterval
ASSUME FinSingletonRcdRange
ASSUME FinSingletonTupleRange
ASSUME FinSingletonSubset
ASSUME FinSingletonFcnSet
ASSUME FinSingletonNestedNat
ASSUME FinSingletonAsDomain

ASSUME FinSeqEmpty
ASSUME FinSeqEmptyInterval
ASSUME FinSeqEmptyRcd
ASSUME FinSeqEmptyTuple
ASSUME FinSeqEmptyFcnSet

-----------------------------------------------------------------------------
\* Sets that are neither empty nor {<<>>}, i.e. comparing the domains and the
\* co-domains, the field sets, or the components is the only means left to
\* decide these.

ASSUME DomainNatReflexive
ASSUME DomainNatIntDiffer
ASSUME DomainSubsetNatReflexive

ASSUME RangeNatReflexive
ASSUME RangeNatIntDiffer

ASSUME DomainFcnSetReflexive
ASSUME RangeNestedUnitDomainDiffer

ASSUME RcdNatReflexive
ASSUME RcdNatIntDiffer
ASSUME RcdStrReflexive

ASSUME TupNatReflexive
ASSUME TupNatIntDiffer
ASSUME TupStrReflexive

-----------------------------------------------------------------------------
\* The same sets read through \in.

ASSUME InUnitEmptyRange
ASSUME InUnitSingletonRange
ASSUME InUnitTripleRange
ASSUME InUnitNatRange
ASSUME InUnitInterval
ASSUME InUnitIntervalNat
ASSUME InUnitCap
ASSUME InUnitCup
ASSUME InUnitDiff
ASSUME InUnitUnionEmpty
ASSUME InUnitUnionOfEmpty
ASSUME InUnitFilter

ASSUME InUnitRcdField
ASSUME InUnitRcdFieldNat
ASSUME InUnitRcdNatField
ASSUME InUnitTuple
ASSUME InUnitTupleNatSecond
ASSUME InUnitTupleNatFirst
ASSUME InUnitTupleStrFirst
ASSUME InUnitFcnSet
ASSUME InUnitFcnSetNat
ASSUME InUnitFcnSetNested

ASSUME InUnitRcdFcnSet
ASSUME InUnitRcdRcd
ASSUME InUnitRcdTuple
ASSUME InUnitTupleFcnSet
ASSUME InUnitTupleRcd
ASSUME InUnitTupleTuple

ASSUME NotInUnitTuple
ASSUME NotInUnitRcd

ASSUME NotInEmpty
ASSUME NotInEmptyInterval
ASSUME NotInEmptySubsetEmpty

ASSUME NotInEmptyFcn
ASSUME NotInEmptyRcdDomain
ASSUME NotInEmptyRcdRange
ASSUME NotInEmptyTupleRange
ASSUME NotInEmptyFcnSetRange

ASSUME NotInRcdEmptyField
ASSUME NotInRcdEmptyArity
ASSUME NotInRcdEmptyPosition
ASSUME NotInRcdEmptyInterval

ASSUME NotInRcdEmptyFcnSet
ASSUME NotInRcdEmptyRcd
ASSUME NotInRcdEmptyTuple

ASSUME NotInRcdEmptyFieldNat
ASSUME NotInRcdEmptyNatField
ASSUME NotInRcdEmptyStrField
ASSUME NotInRcdEmptyThenDiff
ASSUME NotInRcdDiffThenEmpty

ASSUME NotInTupEmptyComponent
ASSUME NotInTupEmptyPosition
ASSUME NotInTupEmptyArity
ASSUME NotInTupEmptyInterval

ASSUME NotInTupEmptyFcnSet
ASSUME NotInTupEmptyRcd
ASSUME NotInTupEmptyTuple

ASSUME NotInTupEmptyNatFirst
ASSUME NotInTupEmptyNatSecond
ASSUME NotInTupEmptySeqFirst
ASSUME NotInTupEmptyStrFirst
ASSUME NotInTupDiffThenEmpty
ASSUME NotInTupEmptyThenDiff

ASSUME InRcdSetIsFcnSet
ASSUME InFcnSetIsRcdSet
ASSUME InTupleSetIsFcnSet
ASSUME InFcnSetIsTupleSet

ASSUME NotInFcnSetDomain
ASSUME NotInRcdSetName
ASSUME NotInRcdSetArity
ASSUME NotInTupleSetArity
ASSUME NotInTupleSetOffset

ASSUME InRcdSetNat
ASSUME InTupleSetNat
ASSUME InFcnSetNatRange

-----------------------------------------------------------------------------
\* The remaining operator that has to agree with the comparisons above.

ASSUME SubsetUnitRanges
ASSUME SubsetUnitNatRange
ASSUME SubsetEmptyDomain
ASSUME SubsetEmptyNatDomain

-----------------------------------------------------------------------------
\* The rendering that TLC prints for the same sets, which has to agree with
\* the cardinalities above: TLC prints a set whose cardinality is below
\* TLCGlobals.enumBound by enumerating it and prints the constructor it was
\* written with otherwise, so a set that an empty argument reduces to { } or
\* { <<>> } prints as that. The last assumption has no empty argument and its
\* cardinality exceeds the bound, i.e. it is the constructor case and the
\* empty arguments are what separates the ones above it from it.
\*
\* TLC!ToString reads the rendering that keeps a nested error instead of
\* discarding it (Value#toStringUnchecked), i.e. these state what TLC prints
\* rather than a fact about TLA+, which is why they have no proof and are
\* written out here instead of in EmptySetEqCases.tla.

ASSUME ToString([n1 : {}, n2 : Nat])                     = "{}"
ASSUME ToString([n1 : {}, n2 : (Nat \ {0})])             = "{}"
ASSUME ToString({} \X Nat)                               = "{}"
ASSUME ToString([n1 : 1..50000, n2 : 1..50000, n3 : {}]) = "{}"
ASSUME ToString((1..50000) \X (1..50000) \X {})          = "{}"
ASSUME ToString([{} -> (SUBSET (1..40))])                = "{<<>>}"
ASSUME ToString([{} -> ((1..50000) \X (1..50000))])      = "{<<>>}"
ASSUME ToString([{} -> Nat])                             = "{<<>>}"

ASSUME ToString([n1 : 1..50000, n2 : 1..50000]) = "[n1: 1..50000, n2: 1..50000]"

-----------------------------------------------------------------------------
\* The comparisons that TLC refuses to answer. Giving up is acceptable for
\* these sets, whereas a wrong answer is not. The groups at the end of this
\* section say where a refusal records a limitation instead, i.e. where TLA+
\* does decide the comparison.

\* A domain or a co-domain that TLC cannot enumerate.
ASSUME AssertError("Attempted to enumerate S \\ T when S:\nNat\nis not enumerable.",
                   [(Nat \ {0}) -> {"d1"}] = [(Nat \ {0}) -> {"d1"}])
ASSUME AssertError("Attempted to enumerate S \\ T when S:\nNat\nis not enumerable.",
                   [{"d1"} -> (Nat \ {0})] = [{"d1"} -> (Nat \ {0})])
ASSUME AssertError("Attempted to enumerate S \\ T when S:\nNat\nis not enumerable.",
                   [{"ref"} -> {}] = [(Nat \ {0}) -> {}])
ASSUME AssertError("Attempted to enumerate S \\ T when S:\nNat\nis not enumerable.",
                   [{"ref"} -> {}] = [[n1 : (Nat \ {0})] -> {}])
ASSUME AssertError("Attempted to enumerate S \\ T when S:\nNat\nis not enumerable.",
                   [{"ref"} -> {}] = [((Nat \ {0}) \X {"d1"}) -> {}])
ASSUME AssertError("Attempted to check if the value:\n\"d1\"\nis an element of Nat.",
                   [{"ref"} -> {}] = [({"d1"} \cap Nat) -> {}])
ASSUME AssertError("Attempted to enumerate S \\cup T when S:\n{\"d1\"}\nand T:\nNat\nare not both enumerable",
                   [{"ref"} -> {}] = [({"d1"} \cup Nat) -> {}])
ASSUME AssertError("Attempted to enumerate UNION(s), but some element of s is nonenumerable.",
                   [{"ref"} -> {}] = [(UNION {Nat}) -> {}])
ASSUME AssertError("Attempted to enumerate { x \\in S : p(x) } when S:\nNat\nis not enumerable",
                   [{"ref"} -> {}] = [{d \in Nat : d > 0} -> {}])

\* A field set or a component that TLC cannot enumerate, in the position that
\* it reaches before the empty one. RcdEmptyThenDiffSym and TupEmptyThenDiffSym
\* are the two comparisons in the order that TLC decides.
ASSUME AssertError("Attempted to enumerate S \\ T when S:\nNat\nis not enumerable.",
                   [ref : {}] = [n1 : (Nat \ {0}), n2 : {}])
ASSUME AssertError("Attempted to enumerate S \\ T when S:\nNat\nis not enumerable.",
                   ({"ref"} \X {}) = ((Nat \ {0}) \X {}))

\* An emptiness that TLC does not know: Nat \ Nat is empty, i.e. the two sets
\* differ, and answering the comparison on the two empty co-domains, field
\* sets, or components would make TLC report them as equal.
ASSUME AssertError("Attempted to enumerate S \\ T when S:\nNat\nis not enumerable.",
                   [{"ref"} -> {}] # [(Nat \ Nat) -> {}])
ASSUME AssertError("Attempted to enumerate S \\ T when S:\nNat\nis not enumerable.",
                   [(Nat \ Nat) -> {}] # [{"ref"} -> {}])
ASSUME AssertError("Attempted to enumerate S \\ T when S:\nNat\nis not enumerable.",
                   [ref : {}] # [n1 : (Nat \ Nat)])
ASSUME AssertError("Attempted to enumerate S \\ T when S:\nNat\nis not enumerable.",
                   ({"ref"} \X {}) # ((Nat \ Nat) \X {"d1"}))

\* A record and a tuple, which differ because their domains differ
\* (ESE_RcdSetDiffTupleSet of EmptySetEqTheorems.tla), and which TLC refuses
\* to compare.
ASSUME AssertError("Attempted to check equality of record:\n[n1 |-> \"a\"]\nwith non-record\n<<\"a\", \"a\">>",
                   [n1 : {"a"}] # ({"a"} \X {"a"}))

\* An overridden value compared with a set that TLC enumerates.
ASSUME AssertError("Attempted to compare overridden value Seq({}) with non-overridden value:\n{<<>>}",
                   Seq({}) = {<<>>})
ASSUME AssertError("Attempted to check equality of the set {<<>>} with the value:\nSeq({})",
                   {<<>>} = Seq({}))
ASSUME AssertError("Attempted to compare overridden value Nat with non-overridden value:\n{\"r1\"}",
                   [Nat -> {"d1"}] # [{"r1"} -> {"d1"}])
ASSUME AssertError("Attempted to check equality of the set {\"r1\"} with the value:\nNat",
                   [{"r1"} -> {"d1"}] # [Nat -> {"d1"}])
ASSUME AssertError("Attempted to compare overridden value Seq({}) with non-overridden value:\n{<<>>}",
                   [Seq({}) -> {"d1"}] = [{<<>>} -> {"d1"}])
ASSUME AssertError("Attempted to check equality of the set {<<>>} with the value:\nSeq({})",
                   [{<<>>} -> {"d1"}] = [Seq({}) -> {"d1"}])
ASSUME AssertError("Attempted to compare overridden value Nat with non-overridden value:\n{\"r1\"}",
                   [{"d1"} -> Nat] # [{"d1"} -> {"r1"}])
ASSUME AssertError("Attempted to check equality of the set {\"r1\"} with the value:\nNat",
                   [{"d1"} -> {"r1"}] # [{"d1"} -> Nat])
ASSUME AssertError("Attempted to compare overridden value Seq({}) with non-overridden value:\n{<<>>}",
                   [{"d1"} -> Seq({})] = [{"d1"} -> {<<>>}])
ASSUME AssertError("Attempted to check equality of the set {<<>>} with the value:\nSeq({})",
                   [{"d1"} -> {<<>>}] = [{"d1"} -> Seq({})])

\* TLC!Any, whose emptiness no rule decides. TLA+ defines Any as
\* CHOOSE x : TRUE, a fixed but unspecified value, so [Any -> {}] is { <<>> }
\* if Any = {} and {} otherwise. Unlike Nat, Int, STRING, and Seq(S) above,
\* which the Empty*Sym comparisons have TLC answer from a witness, Any has no
\* witness to offer. TLC therefore refuses these instead of reading its own
\* rule that every value is in Any (tlc2.module.AnySet#member, which no set
\* satisfies) as Any # {}. Refusing a reflexive comparison is acceptable for
\* the same reason.
ASSUME AssertError("Shouldn't call isEmpty() on value ANY",
                   [{"ref"} -> {}] = [Any -> {}])
ASSUME AssertError("Shouldn't call isEmpty() on value ANY",
                   [Any -> {}] = [Any -> {}])
ASSUME AssertError("Shouldn't call isEmpty() on value ANY",
                   [ref : {}] = [n1 : Any, n2 : {}])
ASSUME AssertError("Shouldn't call isEmpty() on value ANY",
                   ({"ref"} \X {}) = (Any \X {}))

\* An operator other than = that gives up where = decides: [Nat -> {}] is
\* empty, so \notin has an answer that TLC does not give. ESE_EmptyNonMember
\* of EmptySetEqTheorems.tla states it, and SubsetEmptyNatDomain is the
\* \subseteq that TLC does answer on the same set.
ASSUME AssertError("Attempted to check equality of the set {} with the value:\nNat",
                   NotInEmptyNatDomain)

\* The finiteness of a set built from a value whose emptiness TLA+ leaves
\* open, which TLA+ leaves open in turn: [1 -> 2] is { <<>> } if 1 = {} and
\* {} if 2 = {}, both finite, and need not be finite otherwise. TLC tests the
\* finiteness of an argument before its emptiness, so these carry the message
\* of IntValue#isFinite rather than the isEmpty message of the five below.
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to check if the integer 1 is a finite set.",
                   IsFiniteSet([1 -> 2]))
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to check if the integer 1 is a finite set.",
                   IsFiniteSet([n1 : 1, n2 : {"d1"}]))
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to check if the integer 1 is a finite set.",
                   IsFiniteSet(1 \X {"d1"}))
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to check if the integer 1 is a finite set.",
                   IsFiniteSet(Seq(1)))
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to check if the string \"s\" is a finite set.",
                   IsFiniteSet(Seq("s")))
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value),\nbut it produced the following error:\nShouldn't call isEmpty() on value <<1>>",
                   IsFiniteSet(Seq(<<1>>)))

ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to compute the number of elements in the overridden value Seq({}).",
                   IsFiniteSet([Nat -> Seq({})]))

\* Five assumptions that record a limitation instead of an acceptable
\* refusal. EmptySetEqCases_proofs.tla derives each of them from
\* ESE_FcnSetCongruence, ESE_RcdSetCongruence, or ESE_TupleSetCongruence, i.e.
\* TLA+ determines all five to be TRUE. A set is a function of the arguments
\* of its constructor, so a comparison of a set with itself holds whatever
\* those arguments contain, and no emptiness is needed to decide it.
\*
\* TLC decides a comparison the other way round: SetOfRcdsValue#equals tests
\* the emptiness of the field sets, SetOfTuplesValue#equals that of the
\* components, and SetOfFcnsValue#equals that of the domain and the co-domain,
\* each before comparing them. Congruence follows from the comparison that
\* these tests precede, whereas a test itself requires 1 = {} or 1 # {},
\* neither of which is a theorem of TLA+. Deciding these five therefore needs
\* an emptiness test that may answer neither, and a comparison of the
\* arguments where it does. Until then TLC refuses, which is sound.
\*
\* The tests came to the three constructors separately, which is why TLC
\* answered the five until different times. Commit 075246eea of 2014-06-09
\* added them to SetOfRcdsValue#equals and SetOfTuplesValue#equals, so TLC has
\* refused RcdIntReflexive and TupIntReflexive since, and it refuses the three
\* remaining ones since the commit that added them to SetOfFcnsValue#equals.
ASSUME AssertError("Shouldn't call isEmpty() on value 1", FcnIntReflexive)
ASSUME AssertError("Shouldn't call isEmpty() on value \"s\"", FcnStrLitReflexive)
ASSUME AssertError("Shouldn't call isEmpty() on value <<1>>", FcnTupleReflexive)
ASSUME AssertError("Shouldn't call isEmpty() on value 1", RcdIntReflexive)
ASSUME AssertError("Shouldn't call isEmpty() on value 1", TupIntReflexive)

\* Two comparisons of { } with a set of functions that is not empty, which
\* record a limitation as well. EmptySetEqCases_proofs.tla derives both from
\* ESE_FcnSetEmpty: a set of functions is empty only for an empty co-domain,
\* and 0 \in Nat rules that out whatever the domain is.
\*
\* TLC reads the co-domain the other way round, by enumerating it once per
\* element of the domain, which is what it cannot do for Nat. An empty domain
\* asks for no enumeration at all, so UnitNatRangeEnum and
\* UnitIntervalNatEnum are the same two enumerators answering.
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the range R:\nNat\ncannot be enumerated.",
                   EmptyDiffNatRangeEnum)
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the range R:\nNat\ncannot be enumerated.",
                   EmptyDiffIntervalNatEnum)

\* The cardinality that records a limitation as well.
\*
\* EmptySetEqCases_proofs.tla derives it from ESE_RcdSetEmptyCardinality.
\*
\* Cardinality is a module override, so the error of each of these carries
\* the wrapper that TLC puts around one.
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to enumerate S \\ T when S:\nNat\nis not enumerable.",
                   CardRcdDiffThenEmpty)

ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLC.ToString(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to compute the number of elements in the overridden value Nat.",
                   ToString([n1 : Nat, n2 : {}]) = "{}")
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLC.ToString(tlc2.value.impl.Value),\nbut it produced the following error:\nOverflow when computing the number of elements in (1..50000 \\X 1..50000)",
                   ToString([((1..50000) \X (1..50000)) -> {}]) = "{}")

-----------------------------------------------------------------------------
\* The memberships that record a limitation as well, i.e. cases that
\* EmptySetEqCases_proofs.tla proves. Unlike equals, isFinite, and size,
\* member tests no emptiness: it compares the domain of the set with the
\* domain of the value, 1..0 for <<>>, and reads the field sets and the
\* components one by one. An argument that TLC can neither compare nor read
\* therefore refuses a membership that an empty domain, co-domain, field
\* set, or component decides.

\* An empty co-domain, i.e. the set is { } and nothing is its member, where
\* the domain is the argument that TLC gives up on.
ASSUME AssertError("Attempted to check equality of the set {} with the value:\nInt",
                   NotInEmptyIntDomain)
ASSUME AssertError("Attempted to check equality of the set {} with the value:\nSeq({\"d1\"})",
                   NotInEmptySeqDomain)
ASSUME AssertError("Attempted to check equality of the set {} with the value:\nSTRING",
                   NotInEmptyStrDomain)
ASSUME AssertError("Attempted to enumerate S \\ T when S:\nNat\nis not enumerable.",
                   NotInEmptyDiffDomain)
ASSUME AssertError("Attempted to compute the number of elements in the overridden value Nat.",
                   NotInEmptySubsetNat)
ASSUME AssertError("Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn],\nbut can't enumerate the value of the `n1' field:\nNat",
                   NotInEmptyRcdNatDomain)
ASSUME AssertError("Attempted to enumerate a set of the form s1 \\X s2 ... \\X sn,\nbut can't enumerate s0:\nNat",
                   NotInEmptyTupleNatDomain)
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the domain D:\nNat\ncannot be enumerated.",
                   NotInEmptyFcnSetDomain)

\* A field set or a component that TLC cannot check the value against,
\* whereas the empty one beside it decides.
ASSUME AssertError("Attempted to check if the value:\n\"s\"\nis an element of Nat.",
                   NotInRcdEmptyNatFieldStr)
ASSUME AssertError("Attempted to check if the value:\n\"s\"\nis an element of Nat.",
                   NotInTupEmptyNatFirstStr)

\* A tuple where a record set expects a record and a record where a
\* Cartesian product expects a tuple, which the domains of the two values
\* decide (ESE_TupleDomainDiffRcdDomain).
ASSUME AssertError("Attempted to check if non-record\n<<\"a\", \"a\">>\nis in the set of records:\n{[n1 |-> \"a\"]}",
                   NotInRcdSetTuple)
ASSUME AssertError("Attempted to check if non-tuple\n[n1 |-> \"a\"]\nis in the set of tuples:\n{<<\"a\", \"a\">>}",
                   NotInTupleSetRcd)
=============================================================================
