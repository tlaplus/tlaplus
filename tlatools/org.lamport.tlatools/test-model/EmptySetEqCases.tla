-------------------------- MODULE EmptySetEqCases ---------------------------
\* One definition per comparison that TLC has to get right when it compares
\* two sets that it represents without enumerating them: a set of functions,
\* a set of records, or a Cartesian product. EmptySetEqAssume.tla assumes
\* them, which is what puts them in front of TLC's evaluator, and
\* EmptySetEqCases_proofs.tla proves them from the rules in
\* EmptySetEqTheorems.tla. The definitions live in a module of their own,
\* because a module's assumptions are hypotheses for every proof in it and in
\* the modules extending it.
\*
\* The left-hand side of a comparison is the reduced form and the right-hand
\* side the input being tested. The Enum suffix names the form that compares
\* the input with { <<>> } or { }, which puts TLC on its enumeration path, and
\* the Sym suffix the form that compares it with the most reduced form of the
\* input's own constructor: [{} -> {"ref"}] and [{"ref"} -> {}] for a set of
\* functions, [ref : {}] for a set of records, and {"ref"} \X {} for a
\* Cartesian product. An input that TLC cannot enumerate has the Sym form
\* only. The Rev suffix names the form whose operands are swapped, i.e. the
\* exception to the order above, for the reason given in the section carrying
\* it.
\*
\* See https://github.com/tlaplus/tlaplus/issues/1407
EXTENDS FiniteSets, Integers, Sequences

-----------------------------------------------------------------------------
\* Sets of functions that denote {<<>>}, the set whose only element is the
\* empty function, i.e. the empty domain decides.

UnitEmptyRangeEnum     == { <<>> }        = [{} -> {}]
UnitEmptyRangeSym      == [{} -> {"ref"}] = [{} -> {}]
UnitSingletonRangeEnum == { <<>> }        = [{} -> {"d1"}]
UnitSingletonRangeSym  == [{} -> {"ref"}] = [{} -> {"d1"}]
UnitTripleRangeEnum    == { <<>> }        = [{} -> {"a", "b", "c"}]
UnitTripleRangeSym     == [{} -> {"ref"}] = [{} -> {"a", "b", "c"}]
UnitNatRangeSym        == [{} -> {"ref"}] = [{} -> Nat]

UnitIntervalEnum       == { <<>> }        = [1..0 -> {"d1"}]
UnitIntervalSym        == [{} -> {"ref"}] = [1..0 -> {"d1"}]
UnitIntervalNatSym     == [{} -> {"ref"}] = [1..0 -> Nat]

UnitCapEnum            == { <<>> }        = [({"d1"} \cap {"d2"}) -> {"e1"}]
UnitCapSym             == [{} -> {"ref"}] = [({"d1"} \cap {"d2"}) -> {"e1"}]
UnitCupEnum            == { <<>> }        = [({} \cup {}) -> {"e1"}]
UnitCupSym             == [{} -> {"ref"}] = [({} \cup {}) -> {"e1"}]
UnitDiffEnum           == { <<>> }        = [({"d1"} \ {"d1"}) -> {"e1"}]
UnitDiffSym            == [{} -> {"ref"}] = [({"d1"} \ {"d1"}) -> {"e1"}]
UnitUnionEmptyEnum     == { <<>> }        = [(UNION {}) -> {"e1"}]
UnitUnionEmptySym      == [{} -> {"ref"}] = [(UNION {}) -> {"e1"}]
UnitUnionOfEmptyEnum   == { <<>> }        = [(UNION {{}}) -> {"e1"}]
UnitUnionOfEmptySym    == [{} -> {"ref"}] = [(UNION {{}}) -> {"e1"}]
UnitFilterEnum         == { <<>> }        = [{d \in {"d1"} : FALSE} -> {"e1"}]
UnitFilterSym          == [{} -> {"ref"}] = [{d \in {"d1"} : FALSE} -> {"e1"}]

\* The domain is a set of records.
UnitRcdFieldEnum       == { <<>> }        = [[n1 : {}] -> {"e1"}]
UnitRcdFieldSym        == [{} -> {"ref"}] = [[n1 : {}] -> {"e1"}]
UnitRcdNatFieldSym     == [{} -> {"ref"}] = [[n1 : Nat, n2 : {}] -> {"d1"}]
UnitRcdFieldNatSym     == [{} -> {"ref"}] = [[n1 : {}, n2 : Nat] -> {"d1"}]

\* The domain is a Cartesian product.
UnitTupleEnum          == { <<>> }        = [({"d1"} \X {}) -> {"e1"}]
UnitTupleSym           == [{} -> {"ref"}] = [({"d1"} \X {}) -> {"e1"}]
UnitTupleNatFirstSym   == [{} -> {"ref"}] = [(Nat \X {}) -> {"d1"}]
UnitTupleNatSecondSym  == [{} -> {"ref"}] = [({} \X Nat) -> {"d1"}]
UnitTupleStrFirstSym   == [{} -> {"ref"}] = [(STRING \X {}) -> {"d1"}]

\* The domain is a set of functions that is itself empty.
UnitFcnSetSym          == [{} -> {"ref"}] = [[Nat -> {}] -> {"d2"}]
UnitFcnSetNestedSym    == [{} -> {"ref"}] = [[[Nat -> {"d1"}] -> {}] -> {"d2"}]

\* The domain is a set of functions that denotes { <<>> } instead of {}, i.e.
\* it is a singleton, which is what makes these sets differ.
UnitDiffNestedUnitEnum == { <<>> }        # [[{} -> {}] -> {"d2"}]
UnitDiffNestedUnitSym  == [{} -> {"ref"}] # [[{} -> {}] -> {"d2"}]

\* The domain is a set of records or of tuples whose field or component is
\* itself an empty set.
UnitRcdFcnSetSym       == [{} -> {"ref"}] = [[n1 : [Nat -> {}]] -> {"d1"}]
UnitRcdRcdSym          == [{} -> {"ref"}] = [[n1 : [n2 : {}]] -> {"d1"}]
UnitRcdTupleSym        == [{} -> {"ref"}] = [[n1 : ({"d1"} \X {})] -> {"d1"}]
UnitTupleFcnSetSym     == [{} -> {"ref"}] = [({"d1"} \X [Nat -> {}]) -> {"e1"}]
UnitTupleRcdSym        == [{} -> {"ref"}] = [({"d1"} \X [n1 : {}]) -> {"e1"}]
UnitTupleTupleSym      == [{} -> {"ref"}] = [({"d1"} \X ({"d2"} \X {})) -> {"e1"}]

-----------------------------------------------------------------------------
\* Sets of functions that are empty, i.e. the empty co-domain decides. All
\* domains are non-empty, which is what separates these from the group above.

EmptySingletonEnum       == { }             = [{"r1"} -> {}]
EmptySingletonSym        == [{"ref"} -> {}] = [{"r1"} -> {}]
EmptyIntervalEnum        == { }             = [1..2 -> {}]
EmptyIntervalSym         == [{"ref"} -> {}] = [1..2 -> {}]

EmptyCapEnum             == { }             = [({"d1"} \cap {"d1"}) -> {}]
EmptyCapSym              == [{"ref"} -> {}] = [({"d1"} \cap {"d1"}) -> {}]
EmptyCupEnum             == { }             = [({} \cup {"d1"}) -> {}]
EmptyCupSym              == [{"ref"} -> {}] = [({} \cup {"d1"}) -> {}]
EmptyDiffEnum            == { }             = [({"d1"} \ {"d2"}) -> {}]
EmptyDiffSym             == [{"ref"} -> {}] = [({"d1"} \ {"d2"}) -> {}]
EmptyUnionEnum           == { }             = [(UNION {{"d1"}}) -> {}]
EmptyUnionSym            == [{"ref"} -> {}] = [(UNION {{"d1"}}) -> {}]
EmptyFilterEnum          == { }             = [{d \in {"d1"} : TRUE} -> {}]
EmptyFilterSym           == [{"ref"} -> {}] = [{d \in {"d1"} : TRUE} -> {}]

\* SUBSET S contains {} for every S, i.e. it is never empty.
EmptySubsetEmptyEnum     == { }             = [(SUBSET {}) -> {}]
EmptySubsetEmptySym      == [{"ref"} -> {}] = [(SUBSET {}) -> {}]
EmptySubsetNatSym        == [{"ref"} -> {}] = [(SUBSET Nat) -> {}]

EmptyRcdEnum             == { }             = [[n1 : {"d1"}] -> {}]
EmptyRcdSym              == [{"ref"} -> {}] = [[n1 : {"d1"}] -> {}]
EmptyRcdNatSym           == [{"ref"} -> {}] = [[n1 : Nat] -> {}]

EmptyTupleEnum           == { }             = [({"d1"} \X {"d1"}) -> {}]
EmptyTupleSym            == [{"ref"} -> {}] = [({"d1"} \X {"d1"}) -> {}]
EmptyTupleNatSym         == [{"ref"} -> {}] = [(Nat \X {"d1"}) -> {}]

EmptyNatSym              == [{"ref"} -> {}] = [Nat -> {}]
EmptyIntSym              == [{"ref"} -> {}] = [Int -> {}]
EmptySeqSym              == [{"ref"} -> {}] = [Seq({"d1"}) -> {}]
EmptyStrSym              == [{"ref"} -> {}] = [STRING -> {}]

\* The co-domain is empty, instead of the domain.
EmptyRcdRangeSym         == [{"ref"} -> {}] = [{"d1"} -> [n1 : Nat, n2 : {}]]
EmptyTupleRangeSym       == [{"ref"} -> {}] = [{"d1"} -> (Nat \X {})]
EmptyRcdFcnSetRangeSym   == [{"ref"} -> {}] = [{"d1"} -> [n1 : [Nat -> {}]]]
EmptyTupleFcnSetRangeSym == [{"ref"} -> {}] = [{"d1"} -> ({"d1"} \X [Nat -> {}])]
EmptyFcnSetRangeSym      == [{"ref"} -> {}] = [{"x1"} -> [{"y"} -> [Nat -> {}]]]

\* The domain is a set of functions that is non-empty.
EmptyFcnSetSym           == [{"ref"} -> {}] = [[Nat -> {"d1"}] -> {}]

-----------------------------------------------------------------------------
\* Sets of records that are empty, i.e. a single empty field decides. Neither
\* the names nor the number of the fields decides once both sets are empty.

RcdEmptyFieldEnum    == { }        = [n1 : {}]
RcdEmptyFieldSym     == [ref : {}] = [n1 : {}]
RcdEmptyNameSym      == [ref : {}] = [n2 : {}]
RcdEmptyArityEnum    == { }        = [n1 : {}, n2 : {"r1"}]
RcdEmptyAritySym     == [ref : {}] = [n1 : {}, n2 : {"r1"}]
RcdEmptyIntervalEnum == { }        = [n1 : 1..0, n2 : {"r1"}]
RcdEmptyIntervalSym  == [ref : {}] = [n1 : 1..0, n2 : {"r1"}]
RcdEmptyNatFieldSym  == [ref : {}] = [n1 : Nat, n2 : {}]
RcdEmptyFieldNatSym  == [ref : {}] = [n1 : {}, n2 : Nat]
RcdEmptySeqFieldSym  == [ref : {}] = [n1 : Seq({"d1"}), n2 : {}]
RcdEmptyStrFieldSym  == [ref : {}] = [n1 : STRING, n2 : {}]

\* The field is a set of functions, of records, or of tuples that is itself
\* empty.
RcdEmptyFcnSetSym    == [ref : {}] = [n1 : [Nat -> {}]]
RcdEmptyRcdSym       == [ref : {}] = [n1 : [n2 : {}]]
RcdEmptyTupleSym     == [ref : {}] = [n1 : ({"d1"} \X {})]

\* The empty field comes before the field whose emptiness TLC cannot decide,
\* which is why TLC decides this comparison. The reverse order is one of the
\* AssertError assumptions of EmptySetEqAssume.tla.
RcdEmptyThenDiffSym  == [ref : {}] = [n1 : {}, n2 : (Nat \ {0})]

-----------------------------------------------------------------------------
\* Cartesian products that are empty, i.e. a single empty component decides.
\* Neither the position of the empty component nor the number of components
\* decides once both products are empty.

TupEmptyComponentEnum == { }             = ({} \X {"r1"})
TupEmptyComponentSym  == ({"ref"} \X {}) = ({} \X {"r1"})
TupEmptyPositionSym   == ({"ref"} \X {}) = ({"r1"} \X {})
TupEmptyArityEnum     == { }             = ({} \X {"r1"} \X {"r2"})
TupEmptyAritySym      == ({"ref"} \X {}) = ({} \X {"r1"} \X {"r2"})
TupEmptyIntervalEnum  == { }             = ((1..0) \X {"r1"})
TupEmptyIntervalSym   == ({"ref"} \X {}) = ((1..0) \X {"r1"})
TupEmptyNatFirstSym   == ({"ref"} \X {}) = (Nat \X {})
TupEmptyNatSecondSym  == ({"ref"} \X {}) = ({} \X Nat)
TupEmptySeqFirstSym   == ({"ref"} \X {}) = (Seq({"d1"}) \X {})
TupEmptyStrFirstSym   == ({"ref"} \X {}) = (STRING \X {})

\* The component is a set of functions, of records, or of tuples that is
\* itself empty.
TupEmptyFcnSetSym     == ({"ref"} \X {}) = ([Nat -> {}] \X {"d1"})
TupEmptyRcdSym        == ({"ref"} \X {}) = ([n1 : {}] \X {"d1"})
TupEmptyTupleSym      == ({"ref"} \X {}) = (({"d1"} \X {}) \X {"d1"})

\* The empty component comes before the component whose emptiness TLC cannot
\* decide, which is why TLC decides this comparison.
TupEmptyThenDiffSym   == ({"ref"} \X {}) = ({} \X (Nat \ {0}))

-----------------------------------------------------------------------------
\* Two sets of different constructors. TLC enumerates both instead of taking
\* the emptiness rules, so only the enumerable ones are here and the rest are
\* AssertError assumptions of EmptySetEqAssume.tla.

FcnSetEqRcdSetEmpty   == [{"ref"} -> {}] = [n1 : {}]
FcnSetEqTupleSetEmpty == [{"ref"} -> {}] = ({} \X {"r1"})
RcdSetEqTupleSetEmpty == [ref : {}]      = ({} \X {"r1"})
UnitDiffRcdSetEmpty   == [{} -> {"ref"}] # [n1 : {}]
UnitDiffTupleSetEmpty == [{} -> {"ref"}] # ({} \X {"r1"})

\* A record is a function on a set of strings and a tuple is a function on
\* 1..n, i.e. these sets are equal however TLC represents them.
RcdSetIsFcnSet    == [{"n1"} -> {"a"}]    = [n1 : {"a"}]
TupleSetIsFcnSet  == [1..2 -> {"a", "b"}] = ({"a", "b"} \X {"a", "b"})
TupleSetIsFcnSet3 == [1..3 -> {"a"}]      = ({"a"} \X {"a"} \X {"a"})

-----------------------------------------------------------------------------
\* The comparisons above with their operands swapped. TLC evaluates a = b as
\* a.equals(b) (Tool, OPCODE_eq), i.e. the left-hand side decides whose equals
\* runs, and every section above puts the reduced form there. The equals of a
\* set of functions, of records, and of a Cartesian product therefore never
\* receives an argument of another kind, which is the one case it answers by
\* enumerating itself rather than by the emptiness of a domain, a field, or a
\* component. Only the swapped form reaches that case.

UnitEmptyRangeRev     == [{} -> {}]               = { <<>> }
UnitSingletonRangeRev == [{} -> {"d1"}]           = { <<>> }
EmptySingletonRev     == [{"r1"} -> {}]           = { }
RcdEmptyFieldRev      == [n1 : {}]                = { }
RcdEmptyArityRev      == [n1 : {}, n2 : {"r1"}]   = { }
TupEmptyComponentRev  == ({} \X {"r1"})           = { }
TupEmptyArityRev      == ({} \X {"r1"} \X {"r2"}) = { }

\* Two sets of different constructors, with the one that the section above
\* keeps on the right on the left instead.
RcdSetEqFcnSetEmptyRev   == [n1 : {}]      = [{"ref"} -> {}]
TupleSetEqFcnSetEmptyRev == ({} \X {"r1"}) = [{"ref"} -> {}]
TupleSetEqRcdSetEmptyRev == ({} \X {"r1"}) = [ref : {}]
RcdSetIsFcnSetRev        == [n1 : {"a"}]   = [{"n1"} -> {"a"}]
TupleSetIsFcnSetRev      == ({"a", "b"} \X {"a", "b"}) = [1..2 -> {"a", "b"}]

-----------------------------------------------------------------------------
\* How many functions there are.

CardUnitEmptyRange  == 1 = Cardinality([{} -> {}])
CardUnitTripleRange == 1 = Cardinality([{} -> {"a", "b", "c"}])
CardEmptyInterval   == 0 = Cardinality([1..2 -> {}])

-----------------------------------------------------------------------------
\* Sets that are neither empty nor {<<>>}, i.e. comparing the domains and the
\* co-domains, the field sets, or the components is the only means left to
\* decide these. They have no reduced form that TLC could compare them with.

DomainNatReflexive       == [Nat -> {"d1"}] = [Nat -> {"d1"}]
DomainNatIntDiffer       == [Nat -> {"d1"}] # [Int -> {"d1"}]
DomainSubsetNatReflexive == [SUBSET Nat -> {"d1"}] = [SUBSET Nat -> {"d1"}]

RangeNatReflexive        == [{"d1"} -> Nat] = [{"d1"} -> Nat]
RangeNatIntDiffer        == [{"d1"} -> Nat] # [{"d1"} -> Int]

DomainFcnSetReflexive ==
    [[Nat -> {"d1"}] -> {"d2"}] = [[Nat -> {"d1"}] -> {"d2"}]

\* [[Nat -> {}] -> {"d1"}] denotes {<<>>} and not {}, which is why the two
\* sets have one element each and are distinct.
RangeNestedUnitDomainDiffer ==
    [[[Nat -> {}] -> {"d1"}] -> {"d2"}] # [[[Nat -> {}] -> {"d1"}] -> {"d3"}]

RcdNatReflexive == [n1 : Nat, n2 : {"d1"}] = [n1 : Nat, n2 : {"d1"}]
RcdNatIntDiffer == [n1 : Nat, n2 : {"d1"}] # [n1 : Int, n2 : {"d1"}]
RcdStrReflexive == [n1 : STRING, n2 : {"d1"}] = [n1 : STRING, n2 : {"d1"}]

TupNatReflexive == (Nat \X {"d1"}) = (Nat \X {"d1"})
TupNatIntDiffer == (Nat \X {"d1"}) # (Int \X {"d1"})
TupStrReflexive == (STRING \X {"d1"}) = (STRING \X {"d1"})

-----------------------------------------------------------------------------
\* The operators that have to agree with the comparisons above. TLC answers
\* these for the sets it can enumerate and gives up for the rest, i.e. it
\* stays silent instead of contradicting the comparisons.

InUnitSingletonRange == <<>> \in [{} -> {"d1"}]
InUnitNatRange       == <<>> \in [{} -> Nat]
NotInEmpty           == <<>> \notin [{"r1"} -> {}]

SubsetUnitRanges     == [{} -> {"d1"}] \subseteq [{} -> Nat]
SubsetEmptyDomain    == [{"r1"} -> {}] \subseteq [Nat -> {}]
=============================================================================
