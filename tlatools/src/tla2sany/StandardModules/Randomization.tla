-------------------------- MODULE Randomization------------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

RandomSubset(k, S) == TRUE

RandomSubsetSet(k, n, S) == TRUE

RandomSubsetSetSize(k, n, S) == 
      [i \in 1..5 |-> Cardinality(RandomSubsetSet(k, n, S))]

\* picks is the number of draws/picks with replacement.
\* p is a literal (e.g. "0.057") representing a probability
\* of an element of S being in a subset.
RandomSubsetSetProbability(k, p, S) == TRUE

RandomSubsetSetProbabilitySize(k, p, S) == 
      [i \in 1..5 |-> Cardinality(RandomSubsetSetProbability(k, p, S))]

=============================================================================
