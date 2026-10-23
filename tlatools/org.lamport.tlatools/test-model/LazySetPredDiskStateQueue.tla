-------------------- MODULE LazySetPredDiskStateQueue --------------------
EXTENDS Naturals

VARIABLES w, v, i, k

\* TLC defers enumerating SUBSET, so w is a SubsetValue and v a SetPredValue
\* that filters w.
Init == /\ w = SUBSET {0, 1, 2}
        /\ v = {x \in w : 0 \notin x}
        /\ i = 0
        /\ k \in 1..64

Next == /\ i < 3
        /\ i' = i + 1
        /\ UNCHANGED <<w, v, k>>

\* Fingerprinting the view converts w but not v, which therefore remains
\* unfiltered until the DiskStateQueue writes it to disk.
View == <<w, i, k>>

\* Holds in every state.
Holds == \A x \in v : 0 \notin x

\* Violated in every state with i = 3.
Violated == i = 3 => {0} \in v
=============================================================================
