------------------------ MODULE ModuleSemanticsCases ------------------------
\* Shared, assumption-free propositions about the standard modules.
EXTENDS Bags, Integers

MaxInt == 2147483647

\* Bag counts are natural numbers, so BagCardinality, (+), and BagUnion add
\* them without bound.  A sum beyond MaxInt must not wrap to a negative count.
BagCardPair  == BagCardinality([x \in {1, 2} |-> 2]) = 4
BagCupPair   == ([x \in {1} |-> 2] (+) [x \in {1} |-> 1]) = [x \in {1} |-> 3]
BagUnionPair == BagUnion({[x \in {1} |-> 2], [x \in {1} |-> 1]}) = [x \in {1} |-> 3]
BagCardMax   == BagCardinality([x \in {1, 2} |-> MaxInt]) > MaxInt
BagCupMax    == ([x \in {1} |-> MaxInt] (+) [x \in {1} |-> 1])[1] > MaxInt
BagUnionMax  == BagUnion({[x \in {1} |-> MaxInt], [x \in {1} |-> 2]})[1] > MaxInt

=============================================================================
