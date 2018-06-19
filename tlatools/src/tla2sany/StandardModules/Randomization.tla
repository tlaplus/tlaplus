-------------------------- MODULE Randomization------------------------------
LOCAL INSTANCE Naturals

RandomSubset(k, S) == TRUE

RandomSubsetSet(k, n, S) == TRUE

\* picks is the number of draws/picks with replacement.
\* p is a literal (e.g. "0.057") representing a probability
\* of an element of S being in a subset.
RandomSubsetSetProbability(k, p, S) == TRUE
=============================================================================
