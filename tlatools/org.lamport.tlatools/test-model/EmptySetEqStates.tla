------------------------- MODULE EmptySetEqStates --------------------------
\* The assumptions of EmptySetEqAssume.tla have TLC compare the sets of
\* EmptySetEqCases.tla, i.e. they reach Value#equals. A state reaches
\* Value#fingerPrint, because TLC stores a state under the fingerprint of its
\* variables. The two have to agree: equals decides from the emptiness of a
\* domain, a co-domain, a field, or a component, fingerPrint by enumerating
\* the set, and two equal sets that fingerprint differently leave TLC with
\* two states where the behavior spec has one.
\*
\* Each set below is the right-hand side of a comparison in
\* EmptySetEqCases.tla, named beside it and proved in
\* EmptySetEqCases_proofs.tla. Only the enumerable ones are here, because a
\* fingerprint is taken of the enumeration.
\*
\* Spec (EmptySetEqStates.cfg, EmptySetEqStatesTest) holds the sets whose
\* elements are functions and tuples, RcdSpec (EmptySetEqStatesRcd.cfg,
\* EmptySetEqStatesRcdTest) the one whose elements are records, because TLC
\* refuses to compare a record with a tuple.
\*
\* See https://github.com/tlaplus/tlaplus/issues/1407
EXTENDS FiniteSets, Integers, Sequences

VARIABLE x

-----------------------------------------------------------------------------
\* What each group below denotes, written as TLC enumerates it.

Unit  == { <<>> }
Empty == { }
Tup   == { <<"a", "a">>, <<"a", "b">>, <<"b", "a">>, <<"b", "b">> }
Tup3  == { <<"a", "a", "a">> }
Rcd   == { [n1 |-> "a"] }

Reduced == { Unit, Empty, Tup, Tup3 }

\* Unit and Empty written as a set of functions. Next and Extensionality
\* compare x with these rather than with Unit or Empty, because two sets of
\* functions is the comparison of issue #1407, whereas a set of functions and
\* an explicit set only has TLC enumerate the former.
UnitSym  == [{} -> {"ref"}]
EmptySym == [{"ref"} -> {}]

-----------------------------------------------------------------------------
\* The sets, grouped by what they denote and given as tuples, because an
\* explicit set drops the duplicates by normalizing before TLC fingerprints
\* them.

\* Sets of functions that denote { <<>> }, i.e. the empty domain decides.
UnitForms ==
  << [{} -> {}],                            \* UnitEmptyRangeEnum
     [{} -> {"d1"}],                        \* UnitSingletonRangeEnum
     [{} -> {"a", "b", "c"}],               \* UnitTripleRangeEnum
     [1..0 -> {"d1"}],                      \* UnitIntervalEnum
     [({"d1"} \cap {"d2"}) -> {"e1"}],      \* UnitCapEnum
     [({} \cup {}) -> {"e1"}],              \* UnitCupEnum
     [({"d1"} \ {"d1"}) -> {"e1"}],         \* UnitDiffEnum
     [(UNION {}) -> {"e1"}],                \* UnitUnionEmptyEnum
     [(UNION {{}}) -> {"e1"}],              \* UnitUnionOfEmptyEnum
     [{d \in {"d1"} : FALSE} -> {"e1"}],    \* UnitFilterEnum
     [[n1 : {}] -> {"e1"}],                 \* UnitRcdFieldEnum
     [({"d1"} \X {}) -> {"e1"}] >>          \* UnitTupleEnum

\* Sets that are empty, whether a co-domain, a field, or a component decides.
EmptyForms ==
  << [{"r1"} -> {}],                        \* EmptySingletonEnum
     [1..2 -> {}],                          \* EmptyIntervalEnum
     [({"d1"} \cap {"d1"}) -> {}],          \* EmptyCapEnum
     [({} \cup {"d1"}) -> {}],              \* EmptyCupEnum
     [({"d1"} \ {"d2"}) -> {}],             \* EmptyDiffEnum
     [(UNION {{"d1"}}) -> {}],              \* EmptyUnionEnum
     [{d \in {"d1"} : TRUE} -> {}],         \* EmptyFilterEnum
     [(SUBSET {}) -> {}],                   \* EmptySubsetEmptyEnum
     [[n1 : {"d1"}] -> {}],                 \* EmptyRcdEnum
     [({"d1"} \X {"d1"}) -> {}],            \* EmptyTupleEnum
     [n1 : {}],                             \* RcdEmptyFieldEnum
     [n2 : {}],                             \* RcdEmptyNameSym
     [n1 : {}, n2 : {"r1"}],                \* RcdEmptyArityEnum
     [n1 : 1..0, n2 : {"r1"}],              \* RcdEmptyIntervalEnum
     ({} \X {"r1"}),                        \* TupEmptyComponentEnum
     ({"r1"} \X {}),                        \* TupEmptyPositionSym
     ({} \X {"r1"} \X {"r2"}),              \* TupEmptyArityEnum
     ((1..0) \X {"r1"}) >>                  \* TupEmptyIntervalEnum

\* A tuple is a function on 1..n, i.e. both denote the same set.
TupForms  == << [1..2 -> {"a", "b"}],
                ({"a", "b"} \X {"a", "b"}) >>       \* TupleSetIsFcnSet
Tup3Forms == << [1..3 -> {"a"}],
                ({"a"} \X {"a"} \X {"a"}) >>        \* TupleSetIsFcnSet3

\* A record is a function on a set of strings, likewise.
RcdForms  == << [n1 : {"a"}],
                [{"n1"} -> {"a"}] >>                \* RcdSetIsFcnSet

Forms == UnitForms \o EmptyForms \o TupForms \o Tup3Forms

-----------------------------------------------------------------------------
\* Spec. Init has one initial state per set of Forms, so the distinct states
\* are the groups above, counted by fingerprint. Next cycles through the
\* groups, comparing x with what its group denotes, i.e. equality decides
\* whether a sub-action is enabled and a wrong answer deadlocks.

Init == \E i \in 1..Len(Forms) : x = Forms[i]

Next == \/ /\ x = UnitSym  /\ x' = Empty
        \/ /\ x = EmptySym /\ x' = Tup
        \/ /\ x = Tup      /\ x' = Tup3
        \/ /\ x = Tup3     /\ x' = Unit

Spec == Init /\ [][Next]_<<x>>

\* The same count through Value#compareTo: an explicit set drops its
\* duplicates by normalizing where the state graph drops them by
\* fingerprinting.
FormsCollapse == Cardinality({ Forms[i] : i \in 1..Len(Forms) }) = Cardinality(Reduced)

\* Every state is one reduced form and no state is two, i.e. equality
\* separates the groups as well as it merges each.
OneReducedForm == Cardinality({ r \in Reduced : x = r }) = 1

\* Equality and \subseteq have to agree, although \subseteq enumerates the two
\* sets (Enumerable#isSubsetEq, which no set of functions overrides) where
\* equals decides from the emptiness of a domain or a co-domain.
Extensionality ==
  /\ (x \subseteq UnitSym  /\ UnitSym  \subseteq x) <=> (x = UnitSym)
  /\ (x \subseteq EmptySym /\ EmptySym \subseteq x) <=> (x = EmptySym)

Inv == FormsCollapse /\ OneReducedForm /\ Extensionality

-----------------------------------------------------------------------------
\* RcdSpec. A set of records and the set of functions that denotes it, in a
\* behavior spec of their own: TLC refuses to compare a record with a tuple,
\* which the invariant of Spec would. ESE_RcdSetDiffTupleSet of
\* EmptySetEqTheorems.tla is such a comparison that TLA+ decides.

RcdInit == \E i \in 1..Len(RcdForms) : x = RcdForms[i]

RcdNext == UNCHANGED x

RcdSpec == RcdInit /\ [][RcdNext]_<<x>>

RcdInv == /\ Cardinality({ RcdForms[i] : i \in 1..Len(RcdForms) }) = 1
          /\ x = Rcd

-----------------------------------------------------------------------------
\* What the two behavior specs expect TLC to agree with. Each comparison is
\* proved in EmptySetEqCases_proofs.tla, leaving the number of groups and the
\* rule behind Extensionality.

THEOREM Extensional ==
  ASSUME NEW S, NEW T
  PROVE  (S \subseteq T /\ T \subseteq S) <=> (S = T)
  OBVIOUS

\* Spec has four states, not fewer.
THEOREM ReducedDistinct ==
  /\ Unit # Empty
  /\ Unit # Tup
  /\ Unit # Tup3
  /\ Empty # Tup
  /\ Empty # Tup3
  /\ Tup # Tup3
  <1>1. <<>> \in Unit /\ <<"a", "a">> \in Tup /\ <<"a", "a", "a">> \in Tup3
    BY DEF Unit, Tup, Tup3
  <1>2. <<>> \notin Tup /\ <<>> \notin Tup3
    <2>1. DOMAIN <<>> = {}
      OBVIOUS
    <2>2. \A t \in Tup : 1 \in DOMAIN t
      BY DEF Tup
    <2>3. \A t \in Tup3 : 1 \in DOMAIN t
      BY DEF Tup3
    <2>4. QED BY <2>1, <2>2, <2>3
  <1>3. <<"a", "a">> \notin Tup3
    <2>1. DOMAIN <<"a", "a">> = 1..2 /\ \A t \in Tup3 : DOMAIN t = 1..3
      BY DEF Tup3
    <2>2. 3 \in 1..3 /\ 3 \notin 1..2
      OBVIOUS
    <2>3. QED BY <2>1, <2>2
  <1>4. QED BY <1>1, <1>2, <1>3 DEF Empty

\* The group of RcdSpec is none of the four, i.e. a behavior spec of its own
\* rather than a fifth state.
THEOREM RcdDistinct ==
  /\ Rcd # Unit
  /\ Rcd # Empty
  /\ Rcd # Tup
  /\ Rcd # Tup3
  <1>1. [n1 |-> "a"] \in Rcd /\ "n1" \in DOMAIN [n1 |-> "a"]
    BY DEF Rcd
  <1>2. [n1 |-> "a"] \notin Unit
    <2>1. DOMAIN <<>> = {}
      OBVIOUS
    <2>2. QED BY <1>1, <2>1 DEF Unit
  \* Not because "n1" is no number, which TLA+ leaves open, but because a
  \* record has one field where either tuple has two components or more.
  <1>3. [n1 |-> "a"] \notin Tup /\ [n1 |-> "a"] \notin Tup3
    <2>1. \A t \in Tup : DOMAIN t = 1..2
      BY DEF Tup
    <2>2. \A t \in Tup3 : DOMAIN t = 1..3
      BY DEF Tup3
    <2>3. DOMAIN [n1 |-> "a"] = {"n1"}
      OBVIOUS
    <2>4. ASSUME NEW S, {1, 2} \subseteq S, S = {"n1"}
          PROVE  FALSE
      <3>1. 1 = "n1" /\ 2 = "n1"
        BY <2>4
      <3>2. QED BY <3>1
    <2>5. {1, 2} \subseteq 1..2 /\ {1, 2} \subseteq 1..3
      OBVIOUS
    <2>6. QED BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>4. QED BY <1>1, <1>2, <1>3 DEF Empty
=============================================================================
