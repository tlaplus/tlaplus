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
============================================================================
