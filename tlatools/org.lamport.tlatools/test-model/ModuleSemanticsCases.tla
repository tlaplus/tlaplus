------------------------ MODULE ModuleSemanticsCases ------------------------
\* Shared, assumption-free propositions about the standard modules.
EXTENDS Bags, Integers, Randomization

MaxInt == 2147483647

\* Bag counts are natural numbers, so BagCardinality, (+), and BagUnion add
\* them without bound.  A sum beyond MaxInt must not wrap to a negative count.
BagCardPair  == BagCardinality([x \in {1, 2} |-> 2]) = 4
BagCupPair   == ([x \in {1} |-> 2] (+) [x \in {1} |-> 1]) = [x \in {1} |-> 3]
BagUnionPair == BagUnion({[x \in {1} |-> 2], [x \in {1} |-> 1]}) = [x \in {1} |-> 3]
BagCardMax   == BagCardinality([x \in {1, 2} |-> MaxInt]) > MaxInt
BagCupMax    == ([x \in {1} |-> MaxInt] (+) [x \in {1} |-> 1])[1] > MaxInt
BagUnionMax  == BagUnion({[x \in {1} |-> MaxInt], [x \in {1} |-> 2]})[1] > MaxInt

\* RandomSubset(k, S) chooses a k-element subset of S, which exists whenever
\* S has at least k elements, including when S has MaxInt elements.
SingletonOf(T, S) == T \subseteq S /\ T # {} /\ \A x, y \in T : x = y
RandomSubsetOne         == SingletonOf(RandomSubset(1, 1..3), 1..3)
RandomSubsetBelowMaxOne == SingletonOf(RandomSubset(1, 1..(MaxInt - 1)), 1..(MaxInt - 1))
RandomSubsetMaxOne      == SingletonOf(RandomSubset(1, 1..MaxInt), 1..MaxInt)
\* No subset has -1 elements, so RandomSubset(-1, S) is unspecified, yet
\* equal to itself.
RandomSubsetNegRefl == RandomSubset(-1, {1, 2}) = RandomSubset(-1, {1, 2})
\* RandomSubset is a CHOOSE, so two occurrences of the same expression denote
\* the same subset.
RandomSubsetDet == RandomSubset(1, 1..1000) = RandomSubset(1, 1..1000)

=============================================================================
