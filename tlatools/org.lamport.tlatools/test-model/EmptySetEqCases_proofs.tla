----------------------- MODULE EmptySetEqCases_proofs -----------------------
\* The proof of every comparison that EmptySetEqCases.tla defines and
\* EmptySetEqAssume.tla assumes, from the rules of EmptySetEqTheorems.tla. A
\* proof names the rules it instantiates, and supplies the witness or the
\* nested emptiness that the rule asks for.
\*
\* TLC does not parse this module. Check it from tlatools/org.lamport.tlatools
\* with:
\*   tlapm -I test-model test-model/EmptySetEqCases_proofs.tla
\*
\* See https://github.com/tlaplus/tlaplus/issues/1407
EXTENDS EmptySetEqCases, EmptySetEqTheorems

\* The reduced forms that the comparisons below compare an input with, and
\* the nested set that recurs in them.
LEMMA RefUnit == [{} -> {"ref"}] = { <<>> }
  BY ESE_UnitDomain

LEMMA RefEmpty == [{"ref"} -> {}] = {}
  <1>1. "ref" \in {"ref"}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptyRange

LEMMA RefRcdEmpty == [ref : {}] = {}
  <1>1. ASSUME NEW r \in [ref : {}]
        PROVE  FALSE
    <2>1. r.ref \in {}
      OBVIOUS
    <2>2. QED BY <2>1
  <1>2. QED BY <1>1

LEMMA RefTupEmpty == {"ref"} \X {} = {}
  BY ESE_TupleSetEmpty

LEMMA NatToEmpty == [Nat -> {}] = {}
  <1>1. 0 \in Nat
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptyRange

-----------------------------------------------------------------------------
\* Sets of functions that denote {<<>>}, i.e. the empty domain decides.

THEOREM UnitEmptyRangeEnum
  BY ESE_UnitDomain DEF UnitEmptyRangeEnum

THEOREM UnitEmptyRangeSym
  BY RefUnit, ESE_UnitDomain DEF UnitEmptyRangeSym

THEOREM UnitSingletonRangeEnum
  BY ESE_UnitDomain DEF UnitSingletonRangeEnum

THEOREM UnitSingletonRangeSym
  BY RefUnit, ESE_UnitDomain DEF UnitSingletonRangeSym

THEOREM UnitTripleRangeEnum
  BY ESE_UnitDomain DEF UnitTripleRangeEnum

THEOREM UnitTripleRangeSym
  BY RefUnit, ESE_UnitDomain DEF UnitTripleRangeSym

THEOREM UnitNatRangeSym
  BY RefUnit, ESE_UnitDomain DEF UnitNatRangeSym

THEOREM UnitIntervalEnum
  <1>1. 1..0 = {}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_UnitDomain DEF UnitIntervalEnum

THEOREM UnitIntervalSym
  <1>1. 1..0 = {}
    OBVIOUS
  <1>2. QED BY <1>1, RefUnit, ESE_UnitDomain DEF UnitIntervalSym

THEOREM UnitIntervalNatSym
  <1>1. 1..0 = {}
    OBVIOUS
  <1>2. QED BY <1>1, RefUnit, ESE_UnitDomain DEF UnitIntervalNatSym

THEOREM UnitCapEnum
  <1>1. {"d1"} \cap {"d2"} = {}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_UnitDomain DEF UnitCapEnum

THEOREM UnitCapSym
  <1>1. {"d1"} \cap {"d2"} = {}
    OBVIOUS
  <1>2. QED BY <1>1, RefUnit, ESE_UnitDomain DEF UnitCapSym

THEOREM UnitCupEnum
  <1>1. {} \cup {} = {}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_UnitDomain DEF UnitCupEnum

THEOREM UnitCupSym
  <1>1. {} \cup {} = {}
    OBVIOUS
  <1>2. QED BY <1>1, RefUnit, ESE_UnitDomain DEF UnitCupSym

THEOREM UnitDiffEnum
  <1>1. {"d1"} \ {"d1"} = {}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_UnitDomain DEF UnitDiffEnum

THEOREM UnitDiffSym
  <1>1. {"d1"} \ {"d1"} = {}
    OBVIOUS
  <1>2. QED BY <1>1, RefUnit, ESE_UnitDomain DEF UnitDiffSym

THEOREM UnitUnionEmptyEnum
  <1>1. UNION {} = {}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_UnitDomain DEF UnitUnionEmptyEnum

THEOREM UnitUnionEmptySym
  <1>1. UNION {} = {}
    OBVIOUS
  <1>2. QED BY <1>1, RefUnit, ESE_UnitDomain DEF UnitUnionEmptySym

THEOREM UnitUnionOfEmptyEnum
  <1>1. UNION {{}} = {}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_UnitDomain DEF UnitUnionOfEmptyEnum

THEOREM UnitUnionOfEmptySym
  <1>1. UNION {{}} = {}
    OBVIOUS
  <1>2. QED BY <1>1, RefUnit, ESE_UnitDomain DEF UnitUnionOfEmptySym

THEOREM UnitFilterEnum
  <1>1. {d \in {"d1"} : FALSE} = {}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_UnitDomain DEF UnitFilterEnum

THEOREM UnitFilterSym
  <1>1. {d \in {"d1"} : FALSE} = {}
    OBVIOUS
  <1>2. QED BY <1>1, RefUnit, ESE_UnitDomain DEF UnitFilterSym

\* The domain is a set of records.

THEOREM UnitRcdFieldEnum
  BY ESE_UnitDomainRcd1 DEF UnitRcdFieldEnum

THEOREM UnitRcdFieldSym
  BY RefUnit, ESE_UnitDomainRcd1 DEF UnitRcdFieldSym

THEOREM UnitRcdNatFieldSym
  BY RefUnit, ESE_UnitDomainRcd DEF UnitRcdNatFieldSym

THEOREM UnitRcdFieldNatSym
  BY RefUnit, ESE_UnitDomainRcd DEF UnitRcdFieldNatSym

\* The domain is a Cartesian product.

THEOREM UnitTupleEnum
  BY ESE_UnitDomainTuple DEF UnitTupleEnum

THEOREM UnitTupleSym
  BY RefUnit, ESE_UnitDomainTuple DEF UnitTupleSym

THEOREM UnitTupleNatFirstSym
  BY RefUnit, ESE_UnitDomainTuple DEF UnitTupleNatFirstSym

THEOREM UnitTupleNatSecondSym
  BY RefUnit, ESE_UnitDomainTuple DEF UnitTupleNatSecondSym

THEOREM UnitTupleStrFirstSym
  BY RefUnit, ESE_UnitDomainTuple DEF UnitTupleStrFirstSym

\* The domain is a set of functions that is itself empty.

THEOREM UnitFcnSetSym
  <1>1. 0 \in Nat
    OBVIOUS
  <1>2. QED BY <1>1, RefUnit, ESE_UnitDomainFcnSet DEF UnitFcnSetSym

THEOREM UnitFcnSetNestedSym
  <1>1. [n \in Nat |-> "d1"] \in [Nat -> {"d1"}]
    OBVIOUS
  <1>2. QED BY <1>1, RefUnit, ESE_UnitDomainFcnSet DEF UnitFcnSetNestedSym

\* The domain is a set of functions that denotes { <<>> }, i.e. the domains of
\* the two sets are { <<>> } and {}, which ESE_DomainDecides tells apart.

THEOREM UnitDiffNestedUnitEnum
  <1>1. [{} -> {}] = { <<>> }
    BY ESE_UnitDomain
  <1>2. "d2" \in {"d2"}
    OBVIOUS
  <1>3. { <<>> } # {}
    OBVIOUS
  <1>4. [{ <<>> } -> {"d2"}] # [{} -> {"d2"}]
    BY <1>2, <1>3, ESE_DomainDecides
  <1>5. QED BY <1>1, <1>4, ESE_UnitDomain DEF UnitDiffNestedUnitEnum

THEOREM UnitDiffNestedUnitSym
  <1>1. [{} -> {}] = { <<>> }
    BY ESE_UnitDomain
  <1>2. "d2" \in {"d2"}
    OBVIOUS
  <1>3. { <<>> } # {}
    OBVIOUS
  <1>4. [{ <<>> } -> {"d2"}] # [{} -> {"d2"}]
    BY <1>2, <1>3, ESE_DomainDecides
  <1>5. QED BY <1>1, <1>4, RefUnit, ESE_UnitDomain DEF UnitDiffNestedUnitSym

\* The domain is a set of records or of tuples whose field or component is
\* itself an empty set.

THEOREM UnitRcdFcnSetSym
  BY NatToEmpty, RefUnit, ESE_UnitDomainRcd1 DEF UnitRcdFcnSetSym

THEOREM UnitRcdRcdSym
  <1>1. [n2 : {}] = {}
    OBVIOUS
  <1>2. QED BY <1>1, RefUnit, ESE_UnitDomainRcd1 DEF UnitRcdRcdSym

THEOREM UnitRcdTupleSym
  <1>1. {"d1"} \X {} = {}
    BY ESE_TupleSetEmpty
  <1>2. QED BY <1>1, RefUnit, ESE_UnitDomainRcd1 DEF UnitRcdTupleSym

THEOREM UnitTupleFcnSetSym
  BY NatToEmpty, RefUnit, ESE_UnitDomainTuple DEF UnitTupleFcnSetSym

THEOREM UnitTupleRcdSym
  <1>1. [n1 : {}] = {}
    BY ESE_RcdSetEmpty1
  <1>2. QED BY <1>1, RefUnit, ESE_UnitDomainTuple DEF UnitTupleRcdSym

THEOREM UnitTupleTupleSym
  <1>1. {"d2"} \X {} = {}
    BY ESE_TupleSetEmpty
  <1>2. QED BY <1>1, RefUnit, ESE_UnitDomainTuple DEF UnitTupleTupleSym

-----------------------------------------------------------------------------
\* Sets of functions that are empty, i.e. the empty co-domain decides.

THEOREM EmptySingletonEnum
  <1>1. "r1" \in {"r1"}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptyRange DEF EmptySingletonEnum

THEOREM EmptySingletonSym
  <1>1. "r1" \in {"r1"}
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptySingletonSym

THEOREM EmptyIntervalEnum
  <1>1. 1 \in 1..2
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptyRange DEF EmptyIntervalEnum

THEOREM EmptyIntervalSym
  <1>1. 1 \in 1..2
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptyIntervalSym

THEOREM EmptyCapEnum
  <1>1. "d1" \in {"d1"} \cap {"d1"}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptyRange DEF EmptyCapEnum

THEOREM EmptyCapSym
  <1>1. "d1" \in {"d1"} \cap {"d1"}
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptyCapSym

THEOREM EmptyCupEnum
  <1>1. "d1" \in {} \cup {"d1"}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptyRange DEF EmptyCupEnum

THEOREM EmptyCupSym
  <1>1. "d1" \in {} \cup {"d1"}
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptyCupSym

THEOREM EmptyDiffEnum
  <1>1. "d1" \in {"d1"} \ {"d2"}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptyRange DEF EmptyDiffEnum

THEOREM EmptyDiffSym
  <1>1. "d1" \in {"d1"} \ {"d2"}
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptyDiffSym

THEOREM EmptyUnionEnum
  <1>1. "d1" \in UNION {{"d1"}}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptyRange DEF EmptyUnionEnum

THEOREM EmptyUnionSym
  <1>1. "d1" \in UNION {{"d1"}}
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptyUnionSym

THEOREM EmptyFilterEnum
  <1>1. "d1" \in {d \in {"d1"} : TRUE}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptyRange DEF EmptyFilterEnum

THEOREM EmptyFilterSym
  <1>1. "d1" \in {d \in {"d1"} : TRUE}
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptyFilterSym

\* SUBSET S contains {} for every S, i.e. it is never empty.

THEOREM EmptySubsetEmptyEnum
  <1>1. {} \in SUBSET {}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptyRange DEF EmptySubsetEmptyEnum

THEOREM EmptySubsetEmptySym
  <1>1. {} \in SUBSET {}
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptySubsetEmptySym

THEOREM EmptySubsetNatSym
  <1>1. {} \in SUBSET Nat
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptySubsetNatSym

THEOREM EmptyRcdEnum
  <1>1. [n1 |-> "d1"] \in [n1 : {"d1"}]
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptyRange DEF EmptyRcdEnum

THEOREM EmptyRcdSym
  <1>1. [n1 |-> "d1"] \in [n1 : {"d1"}]
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptyRcdSym

THEOREM EmptyRcdNatSym
  <1>1. [n1 |-> 0] \in [n1 : Nat]
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptyRcdNatSym

THEOREM EmptyTupleEnum
  <1>1. <<"d1", "d1">> \in {"d1"} \X {"d1"}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptyRange DEF EmptyTupleEnum

THEOREM EmptyTupleSym
  <1>1. <<"d1", "d1">> \in {"d1"} \X {"d1"}
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptyTupleSym

THEOREM EmptyTupleNatSym
  <1>1. <<0, "d1">> \in Nat \X {"d1"}
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptyTupleNatSym

THEOREM EmptyNatSym
  BY NatToEmpty, RefEmpty DEF EmptyNatSym

THEOREM EmptyIntSym
  <1>1. 0 \in Int
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptyIntSym

THEOREM EmptySeqSym
  <1>1. <<>> \in Seq({"d1"})
    <2>1. <<>> \in [1..0 -> {"d1"}]
      OBVIOUS
    <2>2. QED BY <2>1
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptySeqSym

THEOREM EmptyStrSym
  <1>1. "" \in STRING
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptyStrSym

\* The co-domain is empty, instead of the domain.

THEOREM EmptyRcdRangeSym
  <1>1. "d1" \in {"d1"}
    OBVIOUS
  <1>2. [n1 : Nat, n2 : {}] = {}
    BY ESE_RcdSetEmpty
  <1>3. QED BY <1>1, <1>2, RefEmpty, ESE_EmptyRange DEF EmptyRcdRangeSym

THEOREM EmptyTupleRangeSym
  <1>1. "d1" \in {"d1"}
    OBVIOUS
  <1>2. Nat \X {} = {}
    BY ESE_TupleSetEmpty
  <1>3. QED BY <1>1, <1>2, RefEmpty, ESE_EmptyRange DEF EmptyTupleRangeSym

THEOREM EmptyRcdFcnSetRangeSym
  <1>1. "d1" \in {"d1"}
    OBVIOUS
  <1>2. [n1 : [Nat -> {}]] = {}
    BY NatToEmpty, ESE_RcdSetEmpty1
  <1>3. QED BY <1>1, <1>2, RefEmpty, ESE_EmptyRange DEF EmptyRcdFcnSetRangeSym

THEOREM EmptyTupleFcnSetRangeSym
  <1>1. "d1" \in {"d1"}
    OBVIOUS
  <1>2. {"d1"} \X [Nat -> {}] = {}
    BY NatToEmpty, ESE_TupleSetEmpty
  <1>3. QED BY <1>1, <1>2, RefEmpty, ESE_EmptyRange
        DEF EmptyTupleFcnSetRangeSym

THEOREM EmptyFcnSetRangeSym
  <1>1. "y" \in {"y"}
    OBVIOUS
  <1>2. "x1" \in {"x1"}
    OBVIOUS
  <1>3. [{"y"} -> [Nat -> {}]] = {}
    BY <1>1, NatToEmpty, ESE_EmptyRange
  <1>4. QED BY <1>2, <1>3, RefEmpty, ESE_EmptyRange DEF EmptyFcnSetRangeSym

\* The domain is a set of functions that is non-empty.

THEOREM EmptyFcnSetSym
  <1>1. [n \in Nat |-> "d1"] \in [Nat -> {"d1"}]
    OBVIOUS
  <1>2. QED BY <1>1, RefEmpty, ESE_EmptyRange DEF EmptyFcnSetSym

-----------------------------------------------------------------------------
\* Sets of records that are empty, i.e. a single empty field decides.

THEOREM RcdEmptyFieldEnum
  BY ESE_RcdSetEmpty1 DEF RcdEmptyFieldEnum

THEOREM RcdEmptyFieldSym
  BY RefRcdEmpty, ESE_RcdSetEmpty1 DEF RcdEmptyFieldSym

THEOREM RcdEmptyNameSym
  <1>1. [n2 : {}] = {}
    OBVIOUS
  <1>2. QED BY <1>1, RefRcdEmpty DEF RcdEmptyNameSym

THEOREM RcdEmptyArityEnum
  BY ESE_RcdSetEmpty DEF RcdEmptyArityEnum

THEOREM RcdEmptyAritySym
  BY RefRcdEmpty, ESE_RcdSetEmpty DEF RcdEmptyAritySym

THEOREM RcdEmptyIntervalEnum
  <1>1. 1..0 = {}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_RcdSetEmpty DEF RcdEmptyIntervalEnum

THEOREM RcdEmptyIntervalSym
  <1>1. 1..0 = {}
    OBVIOUS
  <1>2. QED BY <1>1, RefRcdEmpty, ESE_RcdSetEmpty DEF RcdEmptyIntervalSym

THEOREM RcdEmptyNatFieldSym
  BY RefRcdEmpty, ESE_RcdSetEmpty DEF RcdEmptyNatFieldSym

THEOREM RcdEmptyFieldNatSym
  BY RefRcdEmpty, ESE_RcdSetEmpty DEF RcdEmptyFieldNatSym

THEOREM RcdEmptySeqFieldSym
  BY RefRcdEmpty, ESE_RcdSetEmpty DEF RcdEmptySeqFieldSym

THEOREM RcdEmptyStrFieldSym
  BY RefRcdEmpty, ESE_RcdSetEmpty DEF RcdEmptyStrFieldSym

\* The field is a set of functions, of records, or of tuples that is itself
\* empty.

THEOREM RcdEmptyFcnSetSym
  BY NatToEmpty, RefRcdEmpty, ESE_RcdSetEmpty1 DEF RcdEmptyFcnSetSym

THEOREM RcdEmptyRcdSym
  <1>1. [n2 : {}] = {}
    OBVIOUS
  <1>2. QED BY <1>1, RefRcdEmpty, ESE_RcdSetEmpty1 DEF RcdEmptyRcdSym

THEOREM RcdEmptyTupleSym
  <1>1. {"d1"} \X {} = {}
    BY ESE_TupleSetEmpty
  <1>2. QED BY <1>1, RefRcdEmpty, ESE_RcdSetEmpty1 DEF RcdEmptyTupleSym

THEOREM RcdEmptyThenDiffSym
  BY RefRcdEmpty, ESE_RcdSetEmpty DEF RcdEmptyThenDiffSym

-----------------------------------------------------------------------------
\* Cartesian products that are empty, i.e. a single empty component decides.

THEOREM TupEmptyComponentEnum
  BY ESE_TupleSetEmpty DEF TupEmptyComponentEnum

THEOREM TupEmptyComponentSym
  BY RefTupEmpty, ESE_TupleSetEmpty DEF TupEmptyComponentSym

THEOREM TupEmptyPositionSym
  BY RefTupEmpty, ESE_TupleSetEmpty DEF TupEmptyPositionSym

THEOREM TupEmptyArityEnum
  BY ESE_TupleSetEmpty3 DEF TupEmptyArityEnum

THEOREM TupEmptyAritySym
  BY RefTupEmpty, ESE_TupleSetEmpty3 DEF TupEmptyAritySym

THEOREM TupEmptyIntervalEnum
  <1>1. 1..0 = {}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_TupleSetEmpty DEF TupEmptyIntervalEnum

THEOREM TupEmptyIntervalSym
  <1>1. 1..0 = {}
    OBVIOUS
  <1>2. QED BY <1>1, RefTupEmpty, ESE_TupleSetEmpty DEF TupEmptyIntervalSym

THEOREM TupEmptyNatFirstSym
  BY RefTupEmpty, ESE_TupleSetEmpty DEF TupEmptyNatFirstSym

THEOREM TupEmptyNatSecondSym
  BY RefTupEmpty, ESE_TupleSetEmpty DEF TupEmptyNatSecondSym

THEOREM TupEmptySeqFirstSym
  BY RefTupEmpty, ESE_TupleSetEmpty DEF TupEmptySeqFirstSym

THEOREM TupEmptyStrFirstSym
  BY RefTupEmpty, ESE_TupleSetEmpty DEF TupEmptyStrFirstSym

\* The component is a set of functions, of records, or of tuples that is
\* itself empty.

THEOREM TupEmptyFcnSetSym
  BY NatToEmpty, RefTupEmpty, ESE_TupleSetEmpty DEF TupEmptyFcnSetSym

THEOREM TupEmptyRcdSym
  <1>1. [n1 : {}] = {}
    BY ESE_RcdSetEmpty1
  <1>2. QED BY <1>1, RefTupEmpty, ESE_TupleSetEmpty DEF TupEmptyRcdSym

THEOREM TupEmptyTupleSym
  <1>1. {"d1"} \X {} = {}
    BY ESE_TupleSetEmpty
  <1>2. QED BY <1>1, RefTupEmpty, ESE_TupleSetEmpty DEF TupEmptyTupleSym

THEOREM TupEmptyThenDiffSym
  BY RefTupEmpty, ESE_TupleSetEmpty DEF TupEmptyThenDiffSym

-----------------------------------------------------------------------------
\* Two sets of different constructors.

THEOREM FcnSetEqRcdSetEmpty
  BY RefEmpty, ESE_RcdSetEmpty1 DEF FcnSetEqRcdSetEmpty

THEOREM FcnSetEqTupleSetEmpty
  BY RefEmpty, ESE_TupleSetEmpty DEF FcnSetEqTupleSetEmpty

THEOREM RcdSetEqTupleSetEmpty
  BY RefRcdEmpty, ESE_TupleSetEmpty DEF RcdSetEqTupleSetEmpty

THEOREM UnitDiffRcdSetEmpty
  <1>1. [n1 : {}] = {}
    BY ESE_RcdSetEmpty1
  <1>2. <<>> \in { <<>> }
    OBVIOUS
  <1>3. QED BY <1>1, <1>2, RefUnit DEF UnitDiffRcdSetEmpty

THEOREM UnitDiffTupleSetEmpty
  <1>1. {} \X {"r1"} = {}
    BY ESE_TupleSetEmpty
  <1>2. <<>> \in { <<>> }
    OBVIOUS
  <1>3. QED BY <1>1, <1>2, RefUnit DEF UnitDiffTupleSetEmpty

THEOREM RcdSetIsFcnSet
  BY ESE_RcdSetIsFcnSet DEF RcdSetIsFcnSet

THEOREM TupleSetIsFcnSet
  BY ESE_TupleSetIsFcnSet DEF TupleSetIsFcnSet

THEOREM TupleSetIsFcnSet3
  BY ESE_TupleSetIsFcnSet3 DEF TupleSetIsFcnSet3

-----------------------------------------------------------------------------
\* The comparisons above with their operands swapped. Equality is symmetric,
\* so each of these is its counterpart above and needs the same rules.

THEOREM UnitEmptyRangeRev
  BY ESE_UnitDomain DEF UnitEmptyRangeRev

THEOREM UnitSingletonRangeRev
  BY ESE_UnitDomain DEF UnitSingletonRangeRev

THEOREM EmptySingletonRev
  <1>1. "r1" \in {"r1"}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptyRange DEF EmptySingletonRev

THEOREM RcdEmptyFieldRev
  BY ESE_RcdSetEmpty1 DEF RcdEmptyFieldRev

THEOREM RcdEmptyArityRev
  BY ESE_RcdSetEmpty DEF RcdEmptyArityRev

THEOREM TupEmptyComponentRev
  BY ESE_TupleSetEmpty DEF TupEmptyComponentRev

THEOREM TupEmptyArityRev
  BY ESE_TupleSetEmpty3 DEF TupEmptyArityRev

THEOREM RcdSetEqFcnSetEmptyRev
  BY RefEmpty, ESE_RcdSetEmpty1 DEF RcdSetEqFcnSetEmptyRev

THEOREM TupleSetEqFcnSetEmptyRev
  BY RefEmpty, ESE_TupleSetEmpty DEF TupleSetEqFcnSetEmptyRev

THEOREM TupleSetEqRcdSetEmptyRev
  BY RefRcdEmpty, ESE_TupleSetEmpty DEF TupleSetEqRcdSetEmptyRev

THEOREM RcdSetIsFcnSetRev
  BY ESE_RcdSetIsFcnSet DEF RcdSetIsFcnSetRev

THEOREM TupleSetIsFcnSetRev
  BY ESE_TupleSetIsFcnSet DEF TupleSetIsFcnSetRev

-----------------------------------------------------------------------------
\* How many functions there are.

THEOREM CardUnitEmptyRange
  BY ESE_UnitCardinality DEF CardUnitEmptyRange

THEOREM CardUnitTripleRange
  BY ESE_UnitCardinality DEF CardUnitTripleRange

THEOREM CardEmptyInterval
  <1>1. 1 \in 1..2
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptyCardinality DEF CardEmptyInterval

-----------------------------------------------------------------------------
\* Sets of functions that are neither empty nor {<<>>}, i.e. comparing the
\* domains and the co-domains is the only means left to decide these.

THEOREM DomainNatReflexive
  BY DEF DomainNatReflexive

THEOREM DomainNatIntDiffer
  <1>1. "d1" \in {"d1"}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_DomainDecides, ESE_NatIntDiffer
        DEF DomainNatIntDiffer

THEOREM DomainSubsetNatReflexive
  BY DEF DomainSubsetNatReflexive

THEOREM RangeNatReflexive
  BY DEF RangeNatReflexive

THEOREM RangeNatIntDiffer
  <1>1. "d1" \in {"d1"}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_RangeDecides, ESE_NatIntDiffer DEF RangeNatIntDiffer

THEOREM DomainFcnSetReflexive
  BY DEF DomainFcnSetReflexive

THEOREM RangeNestedUnitDomainDiffer
  <1>1. <<>> \in [[Nat -> {}] -> {"d1"}]
    BY NatToEmpty, ESE_UnitMember
  <1>2. QED BY <1>1, ESE_RangeDecides DEF RangeNestedUnitDomainDiffer

THEOREM RcdNatReflexive
  BY DEF RcdNatReflexive

THEOREM RcdNatIntDiffer
  <1>1. "d1" \in {"d1"}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_RcdFieldDecides, ESE_NatIntDiffer DEF RcdNatIntDiffer

THEOREM RcdStrReflexive
  BY DEF RcdStrReflexive

THEOREM TupNatReflexive
  BY DEF TupNatReflexive

THEOREM TupNatIntDiffer
  <1>1. "d1" \in {"d1"}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_TupleComponentDecides, ESE_NatIntDiffer
        DEF TupNatIntDiffer

THEOREM TupStrReflexive
  BY DEF TupStrReflexive

-----------------------------------------------------------------------------
\* The operators that have to agree with the comparisons above.

THEOREM InUnitSingletonRange
  BY ESE_UnitMember DEF InUnitSingletonRange

THEOREM InUnitNatRange
  BY ESE_UnitMember DEF InUnitNatRange

THEOREM NotInEmpty
  <1>1. "r1" \in {"r1"}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptyNonMember DEF NotInEmpty

THEOREM SubsetUnitRanges
  BY ESE_UnitSubset DEF SubsetUnitRanges

THEOREM SubsetEmptyDomain
  <1>1. "r1" \in {"r1"}
    OBVIOUS
  <1>2. QED BY <1>1, ESE_EmptySubset DEF SubsetEmptyDomain
=============================================================================
