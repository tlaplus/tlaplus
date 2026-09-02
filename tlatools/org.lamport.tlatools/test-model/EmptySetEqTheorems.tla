------------------------- MODULE EmptySetEqTheorems -------------------------
(***************************************************************************)
(* The TLA+ facts that TLC has to agree with when it compares two sets     *)
(* that it represents without enumerating them, a set of functions, a set  *)
(* of records, or a Cartesian product, one of which may be empty, and the  *)
(* emptiness of the other kinds of set that such a comparison rests on.    *)
(* This module only lists theorem statements for reference. The proofs can *)
(* be found in module EmptySetEqTheorems_proofs.tla.                       *)
(*                                                                         *)
(* EmptySetEqCases_proofs.tla instantiates these statements to prove the   *)
(* individual comparisons that EmptySetEqAssume.tla has TLC check.         *)
(*                                                                         *)
(* A witness w \in S stands in for S # {} wherever TLC cannot decide       *)
(* S # {} itself, as it cannot for Nat, Int, and Seq(T). The field names   *)
(* n1 and n2 are arbitrary, because the emptiness of a set of records does *)
(* not depend on them, but TLA+ requires a record set to name its fields.  *)
(*                                                                         *)
(* See https://github.com/tlaplus/tlaplus/issues/1407                      *)
(***************************************************************************)
EXTENDS FiniteSets, Integers

(***************************************************************************)
(* When each of the four set constructors that TLC represents without      *)
(* enumerating it is empty.                                                *)
(***************************************************************************)

THEOREM ESE_FcnSetEmpty ==
  ASSUME NEW S, NEW T
  PROVE  [S -> T] = {} <=> (S # {} /\ T = {})

THEOREM ESE_RcdSetEmpty1 ==
  ASSUME NEW S
  PROVE  [n1 : S] = {} <=> S = {}

THEOREM ESE_RcdSetEmpty ==
  ASSUME NEW S, NEW T
  PROVE  [n1 : S, n2 : T] = {} <=> (S = {} \/ T = {})

THEOREM ESE_TupleSetEmpty ==
  ASSUME NEW S, NEW T
  PROVE  S \X T = {} <=> (S = {} \/ T = {})

THEOREM ESE_TupleSetEmpty3 ==
  ASSUME NEW S, NEW T, NEW U
  PROVE  S \X T \X U = {} <=> (S = {} \/ T = {} \/ U = {})

THEOREM ESE_SubsetNonEmpty ==
  ASSUME NEW S
  PROVE  SUBSET S # {}

(***************************************************************************)
(* When each of the remaining kinds of set is empty. TLC decides these per *)
(* kind as well (Value#isEmpty), and the comparisons above short-circuit   *)
(* on that decision.                                                      *)
(***************************************************************************)

THEOREM ESE_IntervalEmpty ==
  ASSUME NEW a \in Int, NEW b \in Int
  PROVE  a..b = {} <=> b < a

THEOREM ESE_CapEmpty ==
  ASSUME NEW S, NEW T
  PROVE  S \cap T = {} <=> \A e \in S : e \notin T

THEOREM ESE_CupEmpty ==
  ASSUME NEW S, NEW T
  PROVE  S \cup T = {} <=> (S = {} /\ T = {})

THEOREM ESE_DiffEmpty ==
  ASSUME NEW S, NEW T
  PROVE  S \ T = {} <=> S \subseteq T

THEOREM ESE_UnionEmpty ==
  ASSUME NEW S
  PROVE  UNION S = {} <=> \A e \in S : e = {}

(***************************************************************************)
(* The two rules that decide the equality of two sets of functions as soon *)
(* as one of them is empty or denotes {<<>>}.                              *)
(***************************************************************************)

THEOREM ESE_UnitDomain ==
  ASSUME NEW S, NEW T, S = {}
  PROVE  [S -> T] = { <<>> }

THEOREM ESE_EmptyRange ==
  ASSUME NEW S, NEW T, NEW w, w \in S, T = {}
  PROVE  [S -> T] = {}

(***************************************************************************)
(* The shapes in which a domain is empty: a set of records, a Cartesian    *)
(* product, and a set of functions. A domain that is empty because of a    *)
(* nested set instantiates one of these with the emptiness of the nested   *)
(* set.                                                                    *)
(***************************************************************************)

THEOREM ESE_UnitDomainRcd1 ==
  ASSUME NEW S, NEW R, S = {}
  PROVE  [[n1 : S] -> R] = { <<>> }

THEOREM ESE_UnitDomainRcd ==
  ASSUME NEW S, NEW T, NEW R, S = {} \/ T = {}
  PROVE  [[n1 : S, n2 : T] -> R] = { <<>> }

THEOREM ESE_UnitDomainTuple ==
  ASSUME NEW S, NEW T, NEW R, S = {} \/ T = {}
  PROVE  [(S \X T) -> R] = { <<>> }

THEOREM ESE_UnitDomainFcnSet ==
  ASSUME NEW S, NEW T, NEW R, NEW w, w \in S, T = {}
  PROVE  [[S -> T] -> R] = { <<>> }

(***************************************************************************)
(* Where neither set is empty nor {<<>>}, the domains and the co-domains,  *)
(* the field sets, and the components decide the equality.                 *)
(***************************************************************************)

THEOREM ESE_DomainDecides ==
  ASSUME NEW S, NEW T, NEW R, NEW w, w \in R
  PROVE  [S -> R] = [T -> R] <=> S = T

THEOREM ESE_RangeDecides ==
  ASSUME NEW S, NEW R, NEW Q, NEW w, w \in S
  PROVE  [S -> R] = [S -> Q] <=> R = Q

THEOREM ESE_RcdFieldDecides ==
  ASSUME NEW S, NEW T, NEW R, NEW w, w \in R
  PROVE  [n1 : S, n2 : R] = [n1 : T, n2 : R] <=> S = T

THEOREM ESE_TupleComponentDecides ==
  ASSUME NEW S, NEW T, NEW R, NEW w, w \in R
  PROVE  S \X R = T \X R <=> S = T

THEOREM ESE_NatIntDiffer == Nat # Int

(***************************************************************************)
(* Where the two sets are of different constructors. A record is a         *)
(* function on a set of strings and a tuple is a function on 1..n, so a    *)
(* set of records and a Cartesian product are sets of functions as well,   *)
(* and a set of records and a product meet only where both are empty.      *)
(***************************************************************************)

THEOREM ESE_RcdSetIsFcnSet ==
  ASSUME NEW S
  PROVE  [n1 : S] = [{"n1"} -> S]

THEOREM ESE_TupleSetIsFcnSet ==
  ASSUME NEW S
  PROVE  S \X S = [1..2 -> S]

THEOREM ESE_TupleSetIsFcnSet3 ==
  ASSUME NEW S
  PROVE  S \X S \X S = [1..3 -> S]

THEOREM ESE_RcdSetDiffTupleSet ==
  ASSUME NEW S, NEW T, NEW w, w \in S
  PROVE  [n1 : S] # S \X T

(***************************************************************************)
(* How many functions there are.                                           *)
(***************************************************************************)

THEOREM ESE_UnitCardinality ==
  ASSUME NEW S, NEW T, S = {}
  PROVE  Cardinality([S -> T]) = 1

THEOREM ESE_EmptyCardinality ==
  ASSUME NEW S, NEW T, NEW w, w \in S, T = {}
  PROVE  Cardinality([S -> T]) = 0

(***************************************************************************)
(* The operators that have to agree with the equalities above.             *)
(***************************************************************************)

THEOREM ESE_UnitMember ==
  ASSUME NEW S, NEW T, S = {}
  PROVE  <<>> \in [S -> T]

THEOREM ESE_EmptyNonMember ==
  ASSUME NEW S, NEW T, NEW w, w \in S, T = {}
  PROVE  <<>> \notin [S -> T]

THEOREM ESE_UnitSubset ==
  ASSUME NEW S, NEW T, NEW U, NEW R, S = {}, U = {}
  PROVE  [S -> T] \subseteq [U -> R]

THEOREM ESE_EmptySubset ==
  ASSUME NEW S, NEW T, NEW U, NEW w, w \in S, T = {}
  PROVE  [S -> T] \subseteq U
=============================================================================
