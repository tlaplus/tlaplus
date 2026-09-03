------------------------- MODULE RandomSubsetEmpty -------------------------
\* Randomization!RandomSubset(k, S) of a set of functions, a set of records, or
\* a Cartesian product that one empty argument makes empty, while another one is
\* a set that TLC cannot enumerate. The empty set decides how many elements
\* there are to pick, i.e. none, so picking one asks nothing of Nat that
\* Naturals does not answer, whereas indexing the set would enumerate it.
\*
\* Cardinality answers 0 for the same three sets, which test-model/
\* EmptySetEqCases.tla states as CardEmptyNatDomain, CardRcdEmptyNatField, and
\* CardTupEmptyNatFirst.
EXTENDS Naturals, FiniteSets, Randomization

ASSUME Cardinality([Nat -> {}]) = 0
ASSUME Cardinality([n1 : Nat, n2 : {}]) = 0
ASSUME Cardinality(Nat \X {}) = 0

ASSUME RandomSubset(1, [Nat -> {}]) = {}
ASSUME RandomSubset(1, [n1 : Nat, n2 : {}]) = {}
ASSUME RandomSubset(1, Nat \X {}) = {}

\* The empty argument in the other position, or beside one whose emptiness TLC
\* cannot decide at all. TLC asks the arguments in order and stops at the first
\* empty one, which is why the empty set has to come before Nat \ {0};
\* EmptySetEqCases.tla states that order as RcdEmptyThenDiffSym and the reverse
\* one as an AssertError.
ASSUME RandomSubset(1, [n1 : {}, n2 : Nat]) = {}
ASSUME RandomSubset(1, [n1 : {}, n2 : (Nat \ {0})]) = {}

\* The empty argument is itself one of the three sets, i.e. the emptiness that
\* decides is one that TLC has to decide the same way one level down.
ASSUME RandomSubset(1, [Nat -> [Nat -> {}]]) = {}
ASSUME RandomSubset(1, [n1 : [Nat -> {}]]) = {}

\* Arguments that TLC can enumerate but whose cardinalities multiply beyond
\* 2147483647, the largest integer TLC represents: 1..50000 twice gives
\* 2500000000. The empty argument decides before any of that is computed, so
\* picking one element neither overflows nor reaches for a big integer.
ASSUME RandomSubset(1, [((1..50000) \X (1..50000)) -> {}]) = {}
ASSUME RandomSubset(1, [n1 : 1..50000, n2 : 1..50000, n3 : {}]) = {}

\* The same cases for a Cartesian product, whose components TLC asks in the
\* same order, plus an empty component among more than two and components that
\* are themselves an empty set of functions, of records, or of tuples.
ASSUME RandomSubset(1, {} \X Nat) = {}
ASSUME RandomSubset(1, {} \X (Nat \ {0})) = {}
ASSUME RandomSubset(1, Nat \X {} \X Nat) = {}
ASSUME RandomSubset(1, [Nat -> {}] \X Nat) = {}
ASSUME RandomSubset(1, [n1 : Nat, n2 : {}] \X Nat) = {}
ASSUME RandomSubset(1, (Nat \X {}) \X Nat) = {}
ASSUME RandomSubset(1, (1..50000) \X (1..50000) \X {}) = {}
ASSUME RandomSubset(1, {} \X (1..50000) \X (1..50000)) = {}
============================================================================
