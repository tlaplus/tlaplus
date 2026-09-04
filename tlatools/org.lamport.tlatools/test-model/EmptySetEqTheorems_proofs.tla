--------------------- MODULE EmptySetEqTheorems_proofs ----------------------
(***************************************************************************)
(* The TLA+ facts that TLC has to agree with when it compares two sets     *)
(* that it represents without enumerating them, one of which may be empty, *)
(* and the emptiness of the other kinds of set that such a comparison      *)
(* rests on, with their proofs. Module EmptySetEqTheorems.tla lists the    *)
(* statements without the proofs, and is the module that                   *)
(* EmptySetEqCases_proofs.tla cites. Keep the statements in the two        *)
(* modules in sync.                                                       *)
(*                                                                         *)
(* TLC does not parse this module. Check it with:                          *)
(*   tlapm test-model/EmptySetEqTheorems_proofs.tla                        *)
(*                                                                         *)
(* See https://github.com/tlaplus/tlaplus/issues/1407                      *)
(***************************************************************************)
EXTENDS FiniteSets, Integers, Sequences, TLAPS
LOCAL INSTANCE FiniteSetTheorems
LOCAL INSTANCE SequenceTheorems

(***************************************************************************)
(* When each of the four set constructors that TLC represents without       *)
(* enumerating it is empty.                                                 *)
(***************************************************************************)

THEOREM ESE_FcnSetEmpty ==
  ASSUME NEW S, NEW T
  PROVE  [S -> T] = {} <=> (S # {} /\ T = {})
  <1>1. ASSUME S # {}, T = {}
        PROVE  [S -> T] = {}
    <2>1. PICK x \in S : TRUE
      BY <1>1
    <2>2. ASSUME NEW f \in [S -> T]
          PROVE  FALSE
      <3>1. f[x] \in T
        BY <2>1
      <3>2. QED BY <1>1, <3>1
    <2>3. QED BY <2>2
  <1>2. ASSUME S = {}
        PROVE  [S -> T] # {}
    <2>1. [x \in S |-> x] \in [S -> T]
      BY <1>2
    <2>2. QED BY <2>1
  <1>3. ASSUME T # {}
        PROVE  [S -> T] # {}
    <2>1. PICK t \in T : TRUE
      BY <1>3
    <2>2. [x \in S |-> t] \in [S -> T]
      BY <2>1
    <2>3. QED BY <2>2
  \* The two cases are the only ways the right-hand side can fail.
  <1>4. QED BY <1>1, <1>2, <1>3

THEOREM ESE_RcdSetEmpty1 ==
  ASSUME NEW S
  PROVE  [n1 : S] = {} <=> S = {}
  <1>1. ASSUME S = {}
        PROVE  [n1 : S] = {}
    <2>1. ASSUME NEW r \in [n1 : S]
          PROVE  FALSE
      <3>1. r.n1 \in S
        OBVIOUS
      <3>2. QED BY <1>1, <3>1
    <2>2. QED BY <2>1
  <1>2. ASSUME S # {}
        PROVE  [n1 : S] # {}
    <2>1. PICK s \in S : TRUE
      BY <1>2
    <2>2. [n1 |-> s] \in [n1 : S]
      BY <2>1
    <2>3. QED BY <2>2
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_RcdSetEmpty ==
  ASSUME NEW S, NEW T
  PROVE  [n1 : S, n2 : T] = {} <=> (S = {} \/ T = {})
  <1>1. ASSUME S = {} \/ T = {}
        PROVE  [n1 : S, n2 : T] = {}
    <2>1. ASSUME NEW r \in [n1 : S, n2 : T]
          PROVE  FALSE
      <3>1. r.n1 \in S /\ r.n2 \in T
        OBVIOUS
      <3>2. QED BY <1>1, <3>1
    <2>2. QED BY <2>1
  <1>2. ASSUME S # {}, T # {}
        PROVE  [n1 : S, n2 : T] # {}
    <2>1. PICK s \in S : TRUE
      BY <1>2
    <2>2. PICK t \in T : TRUE
      BY <1>2
    <2>3. [n1 |-> s, n2 |-> t] \in [n1 : S, n2 : T]
      BY <2>1, <2>2
    <2>4. QED BY <2>3
  \* An empty field set is the only way the right-hand side can hold.
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_RcdSetEmpty3 ==
  ASSUME NEW S, NEW T, NEW U
  PROVE  [n1 : S, n2 : T, n3 : U] = {} <=> (S = {} \/ T = {} \/ U = {})
  <1>1. ASSUME S = {} \/ T = {} \/ U = {}
        PROVE  [n1 : S, n2 : T, n3 : U] = {}
    <2>1. ASSUME NEW r \in [n1 : S, n2 : T, n3 : U]
          PROVE  FALSE
      <3>1. r.n1 \in S /\ r.n2 \in T /\ r.n3 \in U
        OBVIOUS
      <3>2. QED BY <1>1, <3>1
    <2>2. QED BY <2>1
  <1>2. ASSUME S # {}, T # {}, U # {}
        PROVE  [n1 : S, n2 : T, n3 : U] # {}
    <2>1. PICK s \in S : TRUE
      BY <1>2
    <2>2. PICK t \in T : TRUE
      BY <1>2
    <2>3. PICK u \in U : TRUE
      BY <1>2
    <2>4. [n1 |-> s, n2 |-> t, n3 |-> u] \in [n1 : S, n2 : T, n3 : U]
      BY <2>1, <2>2, <2>3
    <2>5. QED BY <2>4
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_TupleSetEmpty ==
  ASSUME NEW S, NEW T
  PROVE  S \X T = {} <=> (S = {} \/ T = {})
  <1>1. ASSUME S = {} \/ T = {}
        PROVE  S \X T = {}
    <2>1. ASSUME NEW t \in S \X T
          PROVE  FALSE
      <3>1. t[1] \in S /\ t[2] \in T
        OBVIOUS
      <3>2. QED BY <1>1, <3>1
    <2>2. QED BY <2>1
  <1>2. ASSUME S # {}, T # {}
        PROVE  S \X T # {}
    <2>1. PICK s \in S : TRUE
      BY <1>2
    <2>2. PICK t \in T : TRUE
      BY <1>2
    <2>3. <<s, t>> \in S \X T
      BY <2>1, <2>2
    <2>4. QED BY <2>3
  \* An empty component is the only way the right-hand side can hold.
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_TupleSetEmpty3 ==
  ASSUME NEW S, NEW T, NEW U
  PROVE  S \X T \X U = {} <=> (S = {} \/ T = {} \/ U = {})
  <1>1. ASSUME S = {} \/ T = {} \/ U = {}
        PROVE  S \X T \X U = {}
    <2>1. ASSUME NEW t \in S \X T \X U
          PROVE  FALSE
      <3>1. t[1] \in S /\ t[2] \in T /\ t[3] \in U
        OBVIOUS
      <3>2. QED BY <1>1, <3>1
    <2>2. QED BY <2>1
  <1>2. ASSUME S # {}, T # {}, U # {}
        PROVE  S \X T \X U # {}
    <2>1. PICK s \in S : TRUE
      BY <1>2
    <2>2. PICK t \in T : TRUE
      BY <1>2
    <2>3. PICK u \in U : TRUE
      BY <1>2
    <2>4. <<s, t, u>> \in S \X T \X U
      BY <2>1, <2>2, <2>3
    <2>5. QED BY <2>4
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_SubsetNonEmpty ==
  ASSUME NEW S
  PROVE  SUBSET S # {}
  <1>1. {} \in SUBSET S
    OBVIOUS
  <1>2. QED BY <1>1

(***************************************************************************)
(* When each of the remaining kinds of set is empty. TLC decides these per  *)
(* kind as well (Value#isEmpty), and the comparisons above short-circuit    *)
(* on that decision.                                                       *)
(***************************************************************************)

THEOREM ESE_IntervalEmpty ==
  ASSUME NEW a \in Int, NEW b \in Int
  PROVE  a..b = {} <=> b < a
  <1>1. ASSUME b < a
        PROVE  a..b = {}
    <2>1. ASSUME NEW i \in a..b
          PROVE  FALSE
      <3>1. i \in Int /\ a =< i /\ i =< b
        OBVIOUS
      <3>2. QED BY <1>1, <3>1
    <2>2. QED BY <2>1
  <1>2. ASSUME a =< b
        PROVE  a..b # {}
    <2>1. a \in a..b
      BY <1>2
    <2>2. QED BY <2>1
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_CapEmpty ==
  ASSUME NEW S, NEW T
  PROVE  S \cap T = {} <=> \A e \in S : e \notin T
  OBVIOUS

THEOREM ESE_CupEmpty ==
  ASSUME NEW S, NEW T
  PROVE  S \cup T = {} <=> (S = {} /\ T = {})
  OBVIOUS

THEOREM ESE_DiffEmpty ==
  ASSUME NEW S, NEW T
  PROVE  S \ T = {} <=> S \subseteq T
  OBVIOUS

THEOREM ESE_UnionEmpty ==
  ASSUME NEW S
  PROVE  UNION S = {} <=> \A e \in S : e = {}
  <1>1. ASSUME UNION S = {}, NEW e \in S
        PROVE  e = {}
    <2>1. ASSUME NEW x \in e
          PROVE  FALSE
      <3>1. x \in UNION S
        BY <1>1, <2>1
      <3>2. QED BY <1>1, <3>1
    <2>2. QED BY <2>1
  <1>2. ASSUME \A e \in S : e = {}
        PROVE  UNION S = {}
    <2>1. ASSUME NEW x \in UNION S
          PROVE  FALSE
      <3>1. PICK e \in S : x \in e
        BY <2>1
      <3>2. e = {}
        BY <1>2, <3>1
      <3>3. QED BY <3>1, <3>2
    <2>2. QED BY <2>1
  <1>3. QED BY <1>1, <1>2

(***************************************************************************)
(* The two rules that decide the equality of two sets of functions as soon  *)
(* as one of them is empty or denotes {<<>>}.                               *)
(***************************************************************************)

THEOREM ESE_UnitDomain ==
  ASSUME NEW S, NEW T, S = {}
  PROVE  [S -> T] = { <<>> }
  <1>1. ASSUME NEW f \in [S -> T]
        PROVE  f = <<>>
    <2>1. DOMAIN f = {}
      OBVIOUS
    <2>2. DOMAIN <<>> = {}
      OBVIOUS
    <2>3. QED BY <2>1, <2>2
  <1>2. <<>> \in [S -> T]
    OBVIOUS
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_EmptyRange ==
  ASSUME NEW S, NEW T, NEW w, w \in S, T = {}
  PROVE  [S -> T] = {}
  <1>1. ASSUME NEW f \in [S -> T]
        PROVE  FALSE
    <2>1. f[w] \in T
      OBVIOUS
    <2>2. QED BY <2>1
  <1>2. QED BY <1>1

(***************************************************************************)
(* The shapes in which a domain is empty: a set of records, a Cartesian     *)
(* product, and a set of functions. A domain that is empty because of a     *)
(* nested set instantiates one of these with the emptiness of the nested    *)
(* set.                                                                     *)
(***************************************************************************)

THEOREM ESE_UnitDomainRcd1 ==
  ASSUME NEW S, NEW R, S = {}
  PROVE  [[n1 : S] -> R] = { <<>> }
  <1>1. [n1 : S] = {}
    BY ESE_RcdSetEmpty1
  <1>2. QED BY <1>1, ESE_UnitDomain

THEOREM ESE_UnitDomainRcd ==
  ASSUME NEW S, NEW T, NEW R, S = {} \/ T = {}
  PROVE  [[n1 : S, n2 : T] -> R] = { <<>> }
  <1>1. [n1 : S, n2 : T] = {}
    BY ESE_RcdSetEmpty
  <1>2. QED BY <1>1, ESE_UnitDomain

THEOREM ESE_UnitDomainTuple ==
  ASSUME NEW S, NEW T, NEW R, S = {} \/ T = {}
  PROVE  [(S \X T) -> R] = { <<>> }
  <1>1. S \X T = {}
    BY ESE_TupleSetEmpty
  <1>2. QED BY <1>1, ESE_UnitDomain

THEOREM ESE_UnitDomainFcnSet ==
  ASSUME NEW S, NEW T, NEW R, NEW w, w \in S, T = {}
  PROVE  [[S -> T] -> R] = { <<>> }
  <1>1. [S -> T] = {}
    BY ESE_EmptyRange
  <1>2. QED BY <1>1, ESE_UnitDomain

(***************************************************************************)
(* Where neither set is empty nor {<<>>}, the domains and the co-domains,  *)
(* the field sets, and the components decide the equality.                 *)
(***************************************************************************)

THEOREM ESE_DomainDecides ==
  ASSUME NEW S, NEW T, NEW R, NEW w, w \in R
  PROVE  [S -> R] = [T -> R] <=> S = T
  <1>1. ASSUME [S -> R] = [T -> R]
        PROVE  S = T
    <2>1. [x \in S |-> w] \in [S -> R]
      OBVIOUS
    <2>2. [x \in S |-> w] \in [T -> R]
      BY <1>1, <2>1
    <2>3. DOMAIN [x \in S |-> w] = S
      OBVIOUS
    <2>4. DOMAIN [x \in S |-> w] = T
      BY <2>2
    <2>5. QED BY <2>3, <2>4
  <1>2. S = T => [S -> R] = [T -> R]
    OBVIOUS
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_RangeDecides ==
  ASSUME NEW S, NEW R, NEW Q, NEW w, w \in S
  PROVE  [S -> R] = [S -> Q] <=> R = Q
  <1>1. ASSUME [S -> R] = [S -> Q]
        PROVE  R = Q
    <2>1. ASSUME NEW r \in R
          PROVE  r \in Q
      <3>1. [x \in S |-> r] \in [S -> R]
        OBVIOUS
      <3>2. [x \in S |-> r] \in [S -> Q]
        BY <1>1, <3>1
      <3>3. [x \in S |-> r][w] = r
        OBVIOUS
      <3>4. [x \in S |-> r][w] \in Q
        BY <3>2
      <3>5. QED BY <3>3, <3>4
    <2>2. ASSUME NEW q \in Q
          PROVE  q \in R
      <3>1. [x \in S |-> q] \in [S -> Q]
        OBVIOUS
      <3>2. [x \in S |-> q] \in [S -> R]
        BY <1>1, <3>1
      <3>3. [x \in S |-> q][w] = q
        OBVIOUS
      <3>4. [x \in S |-> q][w] \in R
        BY <3>2
      <3>5. QED BY <3>3, <3>4
    <2>3. QED BY <2>1, <2>2
  <1>2. R = Q => [S -> R] = [S -> Q]
    OBVIOUS
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_RcdFieldDecides ==
  ASSUME NEW S, NEW T, NEW R, NEW w, w \in R
  PROVE  [n1 : S, n2 : R] = [n1 : T, n2 : R] <=> S = T
  <1>1. ASSUME [n1 : S, n2 : R] = [n1 : T, n2 : R]
        PROVE  S = T
    <2>1. ASSUME NEW s \in S
          PROVE  s \in T
      <3>1. [n1 |-> s, n2 |-> w] \in [n1 : S, n2 : R]
        OBVIOUS
      <3>2. [n1 |-> s, n2 |-> w] \in [n1 : T, n2 : R]
        BY <1>1, <3>1
      <3>3. [n1 |-> s, n2 |-> w].n1 \in T
        BY <3>2
      <3>4. QED BY <3>3
    <2>2. ASSUME NEW t \in T
          PROVE  t \in S
      <3>1. [n1 |-> t, n2 |-> w] \in [n1 : T, n2 : R]
        OBVIOUS
      <3>2. [n1 |-> t, n2 |-> w] \in [n1 : S, n2 : R]
        BY <1>1, <3>1
      <3>3. [n1 |-> t, n2 |-> w].n1 \in S
        BY <3>2
      <3>4. QED BY <3>3
    <2>3. QED BY <2>1, <2>2
  <1>2. S = T => [n1 : S, n2 : R] = [n1 : T, n2 : R]
    OBVIOUS
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_TupleComponentDecides ==
  ASSUME NEW S, NEW T, NEW R, NEW w, w \in R
  PROVE  S \X R = T \X R <=> S = T
  <1>1. ASSUME S \X R = T \X R
        PROVE  S = T
    <2>1. ASSUME NEW s \in S
          PROVE  s \in T
      <3>1. <<s, w>> \in S \X R
        OBVIOUS
      <3>2. <<s, w>> \in T \X R
        BY <1>1, <3>1
      <3>3. <<s, w>>[1] \in T
        BY <3>2
      <3>4. QED BY <3>3
    <2>2. ASSUME NEW t \in T
          PROVE  t \in S
      <3>1. <<t, w>> \in T \X R
        OBVIOUS
      <3>2. <<t, w>> \in S \X R
        BY <1>1, <3>1
      <3>3. <<t, w>>[1] \in S
        BY <3>2
      <3>4. QED BY <3>3
    <2>3. QED BY <2>1, <2>2
  <1>2. S = T => S \X R = T \X R
    OBVIOUS
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_NatIntDiffer == Nat # Int
  <1>1. -1 \in Int
    OBVIOUS
  <1>2. -1 \notin Nat
    OBVIOUS
  <1>3. QED BY <1>1, <1>2

(***************************************************************************)
(* Congruence, which decides a comparison that none of the rules above      *)
(* reaches. Every TLA+ value is a set, but TLA+ does not say what the       *)
(* elements of a value such as 1 are, so neither 1 = {} nor 1 # {} is       *)
(* provable and no witness w \in 1 can be supplied. Each of the three       *)
(* constructors is a function of its arguments all the same, so equal       *)
(* arguments denote the same set whatever the arguments contain.            *)
(***************************************************************************)

THEOREM ESE_FcnSetCongruence ==
  ASSUME NEW S, NEW T
  PROVE  [S -> T] = [S -> T]
  OBVIOUS

THEOREM ESE_RcdSetCongruence ==
  ASSUME NEW S, NEW T
  PROVE  [n1 : S, n2 : T] = [n1 : S, n2 : T]
  OBVIOUS

THEOREM ESE_TupleSetCongruence ==
  ASSUME NEW S, NEW T
  PROVE  S \X T = S \X T
  OBVIOUS

(***************************************************************************)
(* Where the two sets are of different constructors. A record is a          *)
(* function on a set of strings and a tuple is a function on 1..n, so a     *)
(* set of records and a Cartesian product are sets of functions as well,    *)
(* and a set of records and a product meet only where both are empty.       *)
(***************************************************************************)

THEOREM ESE_RcdSetIsFcnSet ==
  ASSUME NEW S
  PROVE  [n1 : S] = [{"n1"} -> S]
  OBVIOUS

THEOREM ESE_TupleSetIsFcnSet ==
  ASSUME NEW S
  PROVE  S \X S = [1..2 -> S]
  <1>1. ASSUME NEW t \in S \X S
        PROVE  t \in [1..2 -> S]
    OBVIOUS
  <1>2. ASSUME NEW f \in [1..2 -> S]
        PROVE  f \in S \X S
    <2>1. f = <<f[1], f[2]>>
      OBVIOUS
    <2>2. f[1] \in S /\ f[2] \in S
      OBVIOUS
    <2>3. <<f[1], f[2]>> \in S \X S
      BY <2>2
    <2>4. QED BY <2>1, <2>3
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_TupleSetIsFcnSet3 ==
  ASSUME NEW S
  PROVE  S \X S \X S = [1..3 -> S]
  <1>1. ASSUME NEW t \in S \X S \X S
        PROVE  t \in [1..3 -> S]
    OBVIOUS
  <1>2. ASSUME NEW f \in [1..3 -> S]
        PROVE  f \in S \X S \X S
    <2>1. f = <<f[1], f[2], f[3]>>
      OBVIOUS
    <2>2. f[1] \in S /\ f[2] \in S /\ f[3] \in S
      OBVIOUS
    <2>3. <<f[1], f[2], f[3]>> \in S \X S \X S
      BY <2>2
    <2>4. QED BY <2>1, <2>3
  <1>3. QED BY <1>1, <1>2

\* The domain of a record is a set of field names and the domain of a tuple
\* is 1..n, i.e. the two differ in size already.
THEOREM ESE_RcdSetDiffTupleSet ==
  ASSUME NEW S, NEW T, NEW w, w \in S
  PROVE  [n1 : S] # S \X T
  <1>1. [n1 |-> w] \in [n1 : S]
    OBVIOUS
  <1>2. ASSUME [n1 : S] = S \X T
        PROVE  FALSE
    <2>1. [n1 |-> w] \in S \X T
      BY <1>1, <1>2
    <2>2. DOMAIN [n1 |-> w] = 1..2
      BY <2>1
    <2>3. DOMAIN [n1 |-> w] = {"n1"}
      OBVIOUS
    <2>4. Cardinality(1..2) = 2
      BY FS_Interval
    <2>5. Cardinality({"n1"}) = 1
      BY FS_Singleton
    <2>6. QED BY <2>2, <2>3, <2>4, <2>5
  <1>3. QED BY <1>2

(***************************************************************************)
(* The cardinality of a set of functions that denotes {<<>>} and of an      *)
(* empty set of each of the three constructors, i.e. the equalities above   *)
(* read through Cardinality.                                                *)
(***************************************************************************)

THEOREM ESE_UnitCardinality ==
  ASSUME NEW S, NEW T, S = {}
  PROVE  Cardinality([S -> T]) = 1
  <1>1. [S -> T] = { <<>> }
    BY ESE_UnitDomain
  <1>2. Cardinality({ <<>> }) = 1
    BY FS_Singleton
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_EmptyCardinality ==
  ASSUME NEW S, NEW T, NEW w, w \in S, T = {}
  PROVE  Cardinality([S -> T]) = 0
  <1>1. [S -> T] = {}
    BY ESE_EmptyRange
  <1>2. Cardinality({}) = 0
    BY FS_EmptySet
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_RcdSetEmptyCardinality1 ==
  ASSUME NEW S, S = {}
  PROVE  Cardinality([n1 : S]) = 0
  <1>1. [n1 : S] = {}
    BY ESE_RcdSetEmpty1
  <1>2. Cardinality({}) = 0
    BY FS_EmptySet
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_RcdSetEmptyCardinality ==
  ASSUME NEW S, NEW T, S = {} \/ T = {}
  PROVE  Cardinality([n1 : S, n2 : T]) = 0
  <1>1. [n1 : S, n2 : T] = {}
    BY ESE_RcdSetEmpty
  <1>2. Cardinality({}) = 0
    BY FS_EmptySet
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_RcdSetEmptyCardinality3 ==
  ASSUME NEW S, NEW T, NEW U, S = {} \/ T = {} \/ U = {}
  PROVE  Cardinality([n1 : S, n2 : T, n3 : U]) = 0
  <1>1. [n1 : S, n2 : T, n3 : U] = {}
    BY ESE_RcdSetEmpty3
  <1>2. Cardinality({}) = 0
    BY FS_EmptySet
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_TupleSetEmptyCardinality ==
  ASSUME NEW S, NEW T, S = {} \/ T = {}
  PROVE  Cardinality(S \X T) = 0
  <1>1. S \X T = {}
    BY ESE_TupleSetEmpty
  <1>2. Cardinality({}) = 0
    BY FS_EmptySet
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_TupleSetEmptyCardinality3 ==
  ASSUME NEW S, NEW T, NEW U, S = {} \/ T = {} \/ U = {}
  PROVE  Cardinality(S \X T \X U) = 0
  <1>1. S \X T \X U = {}
    BY ESE_TupleSetEmpty3
  <1>2. Cardinality({}) = 0
    BY FS_EmptySet
  <1>3. QED BY <1>1, <1>2

(***************************************************************************)
(* The same sets read through IsFiniteSet. Each is { <<>> } or {}, so one  *)
(* empty argument decides, and ESE_EmptyRangeFinite needs no witness in S: *)
(* [S -> {}] is {} where S is non-empty and { <<>> } where it is not.      *)
(***************************************************************************)

THEOREM ESE_UnitFinite ==
  ASSUME NEW S, NEW T, S = {}
  PROVE  IsFiniteSet([S -> T])
  <1>1. [S -> T] = { <<>> }
    BY ESE_UnitDomain
  <1>2. IsFiniteSet({ <<>> })
    BY FS_Singleton
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_EmptyRangeFinite ==
  ASSUME NEW S, NEW T, T = {}
  PROVE  IsFiniteSet([S -> T])
  \* The two cases of S, neither of which needs a witness supplied: an empty S
  \* makes [S -> T] the singleton { <<>> } and a non-empty S supplies its own.
  <1>1. CASE S = {}
    <2>1. [S -> T] = { <<>> }
      BY <1>1, ESE_UnitDomain
    <2>2. QED BY <2>1, FS_Singleton
  <1>2. CASE S # {}
    <2>1. PICK w \in S : TRUE
      BY <1>2
    <2>2. [S -> T] = {}
      BY <2>1, ESE_EmptyRange
    <2>3. QED BY <2>2, FS_EmptySet
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_RcdSetEmptyFinite1 ==
  ASSUME NEW S, S = {}
  PROVE  IsFiniteSet([n1 : S])
  <1>1. [n1 : S] = {}
    BY ESE_RcdSetEmpty1
  <1>2. QED BY <1>1, FS_EmptySet

THEOREM ESE_RcdSetEmptyFinite ==
  ASSUME NEW S, NEW T, S = {} \/ T = {}
  PROVE  IsFiniteSet([n1 : S, n2 : T])
  <1>1. [n1 : S, n2 : T] = {}
    BY ESE_RcdSetEmpty
  <1>2. QED BY <1>1, FS_EmptySet

THEOREM ESE_RcdSetEmptyFinite3 ==
  ASSUME NEW S, NEW T, NEW U, S = {} \/ T = {} \/ U = {}
  PROVE  IsFiniteSet([n1 : S, n2 : T, n3 : U])
  <1>1. [n1 : S, n2 : T, n3 : U] = {}
    BY ESE_RcdSetEmpty3
  <1>2. QED BY <1>1, FS_EmptySet

THEOREM ESE_TupleSetEmptyFinite ==
  ASSUME NEW S, NEW T, S = {} \/ T = {}
  PROVE  IsFiniteSet(S \X T)
  <1>1. S \X T = {}
    BY ESE_TupleSetEmpty
  <1>2. QED BY <1>1, FS_EmptySet

THEOREM ESE_TupleSetEmptyFinite3 ==
  ASSUME NEW S, NEW T, NEW U, S = {} \/ T = {} \/ U = {}
  PROVE  IsFiniteSet(S \X T \X U)
  <1>1. S \X T \X U = {}
    BY ESE_TupleSetEmpty3
  <1>2. QED BY <1>1, FS_EmptySet

THEOREM ESE_SingletonRange ==
  ASSUME NEW S, NEW T, NEW w, T = {w}
  PROVE  [S -> T] = { [x \in S |-> w] }
  \* Extensionality is what makes the two inclusions a singleton: a function
  \* on S whose every value is w is the function [x \in S |-> w] itself.
  <1>1. ASSUME NEW f \in [S -> T]
        PROVE  f = [x \in S |-> w]
    <2>1. DOMAIN f = S
      OBVIOUS
    <2>2. \A x \in S : f[x] = w
      OBVIOUS
    <2>3. QED BY <2>1, <2>2
  <1>2. [x \in S |-> w] \in [S -> T]
    OBVIOUS
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_SingletonRangeFinite ==
  ASSUME NEW S, NEW T, NEW w, T = {w}
  PROVE  IsFiniteSet([S -> T])
  <1>1. [S -> T] = { [x \in S |-> w] }
    BY ESE_SingletonRange
  <1>2. QED BY <1>1, FS_Singleton

THEOREM ESE_SingletonRangeCardinality ==
  ASSUME NEW S, NEW T, NEW w, T = {w}
  PROVE  Cardinality([S -> T]) = 1
  <1>1. [S -> T] = { [x \in S |-> w] }
    BY ESE_SingletonRange
  <1>2. QED BY <1>1, FS_Singleton

LEMMA SingletonDomainBijection ==
  ASSUME NEW S, NEW T, NEW w, S = {w}
  PROVE  ExistsBijection(T, [S -> T])
  <1> DEFINE g == [v \in T |-> [x \in S |-> v]]
  <1>1. g \in Injection(T, [S -> T])
    <2>1. g \in [T -> [S -> T]]
      OBVIOUS
    <2>2. \A v1, v2 \in DOMAIN g : g[v1] = g[v2] => v1 = v2
      <3>1. ASSUME NEW v1 \in T, NEW v2 \in T, g[v1] = g[v2]
            PROVE  v1 = v2
        <4>1. g[v1][w] = v1 /\ g[v2][w] = v2
          OBVIOUS
        <4>2. QED BY <3>1, <4>1
      <3>2. QED BY <3>1
    <2>3. QED BY <2>1, <2>2 DEF Injection, IsInjective
  <1>2. g \in Surjection(T, [S -> T])
    <2>1. ASSUME NEW f \in [S -> T]
          PROVE  f = g[f[w]]
      <3>1. f[w] \in T
        OBVIOUS
      <3>2. g[f[w]] = [x \in S |-> f[w]]
        BY <3>1
      <3>3. DOMAIN f = S /\ \A x \in S : f[x] = f[w]
        OBVIOUS
      <3>4. QED BY <3>2, <3>3
    <2>2. QED BY <2>1 DEF Surjection
  <1>3. QED BY <1>1, <1>2, Zenon DEF ExistsBijection, Bijection

THEOREM ESE_SingletonDomainFinite ==
  ASSUME NEW S, NEW T, NEW w, S = {w}, IsFiniteSet(T)
  PROVE  IsFiniteSet([S -> T])
  BY SingletonDomainBijection, FS_Bijection

THEOREM ESE_SingletonDomainCardinality ==
  ASSUME NEW S, NEW T, NEW w, S = {w}, IsFiniteSet(T)
  PROVE  Cardinality([S -> T]) = Cardinality(T)
  BY SingletonDomainBijection, FS_Bijection

THEOREM ESE_PairFinite ==
  ASSUME NEW a, NEW b, a # b
  PROVE  /\ IsFiniteSet({a, b})
         /\ Cardinality({a, b}) = 2
  <1>1. {a, b} = {a} \cup {b}
    OBVIOUS
  <1>2. IsFiniteSet({a}) /\ Cardinality({a}) = 1
    BY FS_Singleton
  <1>3. b \notin {a}
    OBVIOUS
  <1>4. QED BY <1>1, <1>2, <1>3, FS_AddElement

THEOREM ESE_SeqEmpty ==
  ASSUME NEW S, S = {}
  PROVE  Seq(S) = { <<>> }
  <1>1. ASSUME NEW s \in Seq(S), s # <<>>
        PROVE  FALSE
    <2>1. Len(s) \in Nat \ {0}
      BY <1>1, EmptySeq
    <2>2. 1 \in 1..Len(s)
      BY <2>1
    <2>3. s[1] \in S
      BY <1>1, <2>2, ElementOfSeq
    <2>4. QED BY <2>3
  <1>2. <<>> \in Seq(S)
    BY EmptySeq
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_SeqEmptyFinite ==
  ASSUME NEW S, S = {}
  PROVE  IsFiniteSet(Seq(S))
  <1>1. Seq(S) = { <<>> }
    BY ESE_SeqEmpty
  <1>2. QED BY <1>1, FS_Singleton

(***************************************************************************)
(* The operators that have to agree with the equalities above.              *)
(***************************************************************************)

THEOREM ESE_UnitMember ==
  ASSUME NEW S, NEW T, S = {}
  PROVE  <<>> \in [S -> T]
  <1>1. [S -> T] = { <<>> }
    BY ESE_UnitDomain
  <1>2. QED BY <1>1

THEOREM ESE_EmptyNonMember ==
  ASSUME NEW S, NEW T, NEW w, w \in S, T = {}
  PROVE  <<>> \notin [S -> T]
  <1>1. [S -> T] = {}
    BY ESE_EmptyRange
  <1>2. QED BY <1>1

THEOREM ESE_UnitSubset ==
  ASSUME NEW S, NEW T, NEW U, NEW R, S = {}, U = {}
  PROVE  [S -> T] \subseteq [U -> R]
  <1>1. [S -> T] = { <<>> }
    BY ESE_UnitDomain
  <1>2. [U -> R] = { <<>> }
    BY ESE_UnitDomain
  <1>3. QED BY <1>1, <1>2

THEOREM ESE_EmptySubset ==
  ASSUME NEW S, NEW T, NEW U, NEW w, w \in S, T = {}
  PROVE  [S -> T] \subseteq U
  <1>1. [S -> T] = {}
    BY ESE_EmptyRange
  <1>2. QED BY <1>1
=============================================================================
