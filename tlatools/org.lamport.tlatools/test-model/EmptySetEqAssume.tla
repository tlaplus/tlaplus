-------------------------- MODULE EmptySetEqAssume --------------------------
\* TLC checks every assumption at startup (Tool#checkAssumptions). Each name
\* below is a comparison defined in EmptySetEqCases.tla and proved in
\* EmptySetEqCases_proofs.tla. The AssertError assumptions at the end have no
\* proof, because they state what TLC refuses to answer instead of a TLA+
\* fact.
\*
\* TLC does not yet answer every comparison below. The commented out
\* assumptions are the ones it gets wrong: it decides the ones marked "wrong"
\* the wrong way, refuses the ones marked "refused" with an error, and raises
\* an error other than the expected one for the ones marked "other error".
\* The commits that make TLC answer them uncomment them.
\*
\* See https://github.com/tlaplus/tlaplus/issues/1407
EXTENDS FiniteSets, Integers, Sequences, TLC, TLCExt, EmptySetEqCases

-----------------------------------------------------------------------------
\* Sets of functions that denote {<<>>}, i.e. the empty domain decides.

ASSUME UnitEmptyRangeEnum
\* ASSUME UnitEmptyRangeSym         \* wrong
ASSUME UnitSingletonRangeEnum
\* ASSUME UnitSingletonRangeSym     \* wrong
ASSUME UnitTripleRangeEnum
\* ASSUME UnitTripleRangeSym        \* wrong
\* ASSUME UnitNatRangeSym           \* refused

ASSUME UnitIntervalEnum
\* ASSUME UnitIntervalSym           \* wrong
\* ASSUME UnitIntervalNatSym        \* refused

ASSUME UnitCapEnum
\* ASSUME UnitCapSym                \* wrong
ASSUME UnitCupEnum
\* ASSUME UnitCupSym                \* wrong
ASSUME UnitDiffEnum
\* ASSUME UnitDiffSym               \* wrong
ASSUME UnitUnionEmptyEnum
\* ASSUME UnitUnionEmptySym         \* wrong
ASSUME UnitUnionOfEmptyEnum
\* ASSUME UnitUnionOfEmptySym       \* wrong
ASSUME UnitFilterEnum
\* ASSUME UnitFilterSym             \* wrong

ASSUME UnitRcdFieldEnum
\* ASSUME UnitRcdFieldSym           \* wrong
\* ASSUME UnitRcdNatFieldSym        \* refused
\* ASSUME UnitRcdFieldNatSym        \* wrong

ASSUME UnitTupleEnum
\* ASSUME UnitTupleSym              \* wrong
\* ASSUME UnitTupleNatFirstSym      \* refused
\* ASSUME UnitTupleNatSecondSym     \* wrong
\* ASSUME UnitTupleStrFirstSym      \* refused

\* ASSUME UnitFcnSetSym             \* refused
\* ASSUME UnitFcnSetNestedSym       \* refused
ASSUME UnitDiffNestedUnitEnum
ASSUME UnitDiffNestedUnitSym

\* ASSUME UnitRcdFcnSetSym          \* refused
\* ASSUME UnitRcdRcdSym             \* wrong
\* ASSUME UnitRcdTupleSym           \* wrong
\* ASSUME UnitTupleFcnSetSym        \* refused
\* ASSUME UnitTupleRcdSym           \* wrong
\* ASSUME UnitTupleTupleSym         \* wrong

-----------------------------------------------------------------------------
\* Sets of functions that are empty, i.e. the empty co-domain decides.

ASSUME EmptySingletonEnum
\* ASSUME EmptySingletonSym         \* wrong
ASSUME EmptyIntervalEnum
\* ASSUME EmptyIntervalSym          \* wrong

ASSUME EmptyCapEnum
\* ASSUME EmptyCapSym               \* wrong
ASSUME EmptyCupEnum
\* ASSUME EmptyCupSym               \* wrong
ASSUME EmptyDiffEnum
\* ASSUME EmptyDiffSym              \* wrong
ASSUME EmptyUnionEnum
\* ASSUME EmptyUnionSym             \* wrong
ASSUME EmptyFilterEnum
\* ASSUME EmptyFilterSym            \* wrong

ASSUME EmptySubsetEmptyEnum
\* ASSUME EmptySubsetEmptySym       \* refused
\* ASSUME EmptySubsetNatSym         \* refused

ASSUME EmptyRcdEnum
\* ASSUME EmptyRcdSym               \* refused
\* ASSUME EmptyRcdNatSym            \* refused

ASSUME EmptyTupleEnum
\* ASSUME EmptyTupleSym             \* refused
\* ASSUME EmptyTupleNatSym          \* refused

\* ASSUME EmptyNatSym               \* refused
\* ASSUME EmptyIntSym               \* refused
\* ASSUME EmptySeqSym               \* refused
\* ASSUME EmptyStrSym               \* refused

\* ASSUME EmptyRcdRangeSym          \* wrong
\* ASSUME EmptyTupleRangeSym        \* wrong
\* ASSUME EmptyRcdFcnSetRangeSym    \* wrong
\* ASSUME EmptyTupleFcnSetRangeSym  \* wrong
\* ASSUME EmptyFcnSetRangeSym       \* wrong

\* ASSUME EmptyFcnSetSym            \* refused

-----------------------------------------------------------------------------
\* Sets of records that are empty, i.e. a single empty field decides.

ASSUME RcdEmptyFieldEnum
ASSUME RcdEmptyFieldSym
ASSUME RcdEmptyNameSym
ASSUME RcdEmptyArityEnum
ASSUME RcdEmptyAritySym
ASSUME RcdEmptyIntervalEnum
ASSUME RcdEmptyIntervalSym
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
ASSUME FcnSetEqTupleSetEmpty
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
ASSUME RcdEmptyFieldRev
ASSUME RcdEmptyArityRev
ASSUME TupEmptyComponentRev
ASSUME TupEmptyArityRev

ASSUME RcdSetEqFcnSetEmptyRev
ASSUME TupleSetEqFcnSetEmptyRev
ASSUME TupleSetEqRcdSetEmptyRev
ASSUME RcdSetIsFcnSetRev
ASSUME TupleSetIsFcnSetRev

-----------------------------------------------------------------------------
\* How many functions there are.

ASSUME CardUnitEmptyRange
ASSUME CardUnitTripleRange
ASSUME CardEmptyInterval

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
\* The operators that have to agree with the comparisons above.

ASSUME InUnitSingletonRange
ASSUME InUnitNatRange
ASSUME NotInEmpty

ASSUME SubsetUnitRanges
ASSUME SubsetEmptyDomain

-----------------------------------------------------------------------------
\* The comparisons that TLC refuses to answer. Giving up is acceptable for
\* these sets, whereas a wrong answer is not.

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

\* Two sets of different constructors, where TLC enumerates both instead of
\* taking the emptiness rules. FcnSetEqRcdSetEmpty and the cases next to it
\* are the same comparisons on sets that TLC does enumerate.
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the domain D:\nNat\ncannot be enumerated.",
                   [Nat -> {}] = [n1 : {}])
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the domain D:\nNat\ncannot be enumerated.",
                   [n1 : {}] = [Nat -> {}])
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the domain D:\nNat\ncannot be enumerated.",
                   [Nat -> {}] = ({} \X {"r1"}))
ASSUME AssertError("Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn],\nbut can't enumerate the value of the `n1' field:\nNat",
                   ({} \X {"r1"}) = [n1 : Nat, n2 : {}])

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
\* ASSUME AssertError("Shouldn't call isEmpty() on value ANY",
\*                    [{"ref"} -> {}] = [Any -> {}])  \* other error
\* ASSUME AssertError("Shouldn't call isEmpty() on value ANY",
\*                    [Any -> {}] = [Any -> {}])  \* other error
ASSUME AssertError("Shouldn't call isEmpty() on value ANY",
                   [ref : {}] = [n1 : Any, n2 : {}])
ASSUME AssertError("Shouldn't call isEmpty() on value ANY",
                   ({"ref"} \X {}) = (Any \X {}))

\* An operator other than = that gives up where = decides: [Nat -> {}] is
\* empty and [{} -> Nat] denotes {<<>>} above, so \notin and \subseteq have an
\* answer that TLC does not give. ESE_EmptyNonMember, ESE_EmptySubset, and
\* ESE_UnitSubset of EmptySetEqTheorems.tla state the three answers.
ASSUME AssertError("Attempted to check equality of the set {} with the value:\nNat",
                   <<>> \notin [Nat -> {}])
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the domain D:\nNat\ncannot be enumerated.",
                   [Nat -> {}] \subseteq [{"r1"} -> {}])
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the range R:\nNat\ncannot be enumerated.",
                   [{} -> Nat] \subseteq [{} -> {"d1"}])

\* The reduced form { } or { <<>> } for an input that TLC cannot enumerate.
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the domain D:\nNat\ncannot be enumerated.",
                   { } = [Nat -> {}])
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the domain D:\nNat\ncannot be enumerated.",
                   [Nat -> {}] = { })
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the domain D:\nInt\ncannot be enumerated.",
                   { } = [Int -> {}])
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the domain D:\nSeq({\"d1\"})\ncannot be enumerated.",
                   { } = [Seq({"d1"}) -> {}])
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the range R:\nNat\ncannot be enumerated.",
                   { <<>> } = [{} -> Nat])
ASSUME AssertError("Attempted to compute the number of elements in the overridden value Nat.",
                   { } = [(SUBSET Nat) -> {}])
ASSUME AssertError("Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn],\nbut can't enumerate the value of the `n1' field:\nNat",
                   { } = [[n1 : Nat] -> {}])
ASSUME AssertError("Attempted to enumerate a set of the form s1 \\X s2 ... \\X sn,\nbut can't enumerate s0:\nNat",
                   { } = [(Nat \X {"d1"}) -> {}])
ASSUME AssertError("Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn],\nbut can't enumerate the value of the `n1' field:\nNat",
                   { } = [n1 : Nat, n2 : {}])
ASSUME AssertError("Attempted to enumerate a set of the form s1 \\X s2 ... \\X sn,\nbut can't enumerate s0:\nNat",
                   { } = (Nat \X {}))
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the domain D:\nNat\ncannot be enumerated.",
                   { } = [[Nat -> {"d1"}] -> {}])
ASSUME AssertError("Attempted to enumerate a set of the form [D -> R],but the domain D:\nNat\ncannot be enumerated.",
                   { <<>> } = [[Nat -> {}] -> {"d2"}])
=============================================================================
