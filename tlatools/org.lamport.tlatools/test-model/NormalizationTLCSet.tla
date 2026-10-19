------------------------- MODULE NormalizationTLCSet -------------------------
\* TLC normalizes a set enumeration only when it has to (see
\* NormalizationAssume.tla). TLC evaluates Init outside of a worker, so TLCSet
\* writes the function to the registers of all workers. Writing it doesn't have
\* to normalize the set in its range, so TLC checks the spec even though it
\* cannot compare the elements 1 and "a".
EXTENDS TLC
VARIABLE x
Init == x = FALSE /\ TLCSet(1, [y \in {1} |-> {1, "a"}])
Next == x' = ~x
=============================================================================
