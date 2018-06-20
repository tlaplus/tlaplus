-------------------------- MODULE Randomization------------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

RandomSubset(k, S) == CHOOSE T \in SUBSET S : Cardinality(T) = T

RandomSetOfSubsets(k, n, S) == CHOOSE T \in SUBSET SUBSET S :
											  Cardinality(T) \leq k

TestRandomSetOfSubsets(k, n, S) ==
              [i \in 1..5 |-> Cardinality(RandomSetOfSubsets(k, n, S))]

-----------------------------------------------------------------------------
\* HERE BE DRAGONS: THE OPERATORS BELOW WILL BE REMOVED EVENTUALLY!

\* picks is the number of draws/picks with replacement.
\* p is a literal (e.g. "0.057") representing a probability
\* of an element of S being in a subset.
RandomSubsetSetProbability(k, p, S) == CHOOSE T \in SUBSET SUBSET S :
                                                       Cardinality(T) \leq k

RandomSubsetSetProbabilitySize(k, p, S) == 
      [i \in 1..5 |-> Cardinality(RandomSubsetSetProbability(k, p, S))]

=============================================================================
