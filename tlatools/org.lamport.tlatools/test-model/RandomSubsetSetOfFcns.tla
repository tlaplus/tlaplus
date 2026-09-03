--------------------------- MODULE RandomSubsetSetOfFcns ---------------------------
EXTENDS Integers, FiniteSets, Randomization

VARIABLE x

S == {1,2,3,4,5,6,7,8,9}
T == 1..10

\* Nine copies of T in a Cartesian product make a set of the same 10^9
\* functions, because a tuple is a function whose domain is an interval:
\*
\*     THEOREM \A U : U \X U = [1..2 -> U]
\*
\* which is the case n = 2 of the claim about the nine components below. TLC
\* therefore has to draw from the product without enumerating it either.
\*
\* An assumption rather than a second conjunct of Init, because TLC redraws per
\* value of x, so a second draw would turn the 1000 initial states into 10^6,
\* whereas TLC checks it either way.
Product == T \X T \X T \X T \X T \X T \X T \X T \X T

ASSUME Cardinality(RandomSubset(1000, Product)) = 1000
ASSUME RandomSubset(1000, Product) \subseteq Product
ASSUME RandomSubset(1000, Product) \subseteq [1..9 -> T]

\* [S->T] has 10^9 elements of which we want 1k.
\* Explicitly enumerating all 10^9 elements will
\* definitely timeout the tests.
Init == /\ x \in RandomSubset(1000, [ S -> T ])

Next == /\ UNCHANGED <<x>>

Spec == Init /\ [][Next]_<<x>>

Inv == TRUE
=============================================================================
