--------------------------- MODULE RandomSubsetSetOfFcns ---------------------------
EXTENDS Integers, Randomization

VARIABLE x

S == {1,2,3,4,5,6,7,8,9}
T == 1..10

\* [S->T] has 10^8 elements of which we want 1k.
\* Explicitly enumerating all 10^8 elements will
\* definitely timeout the tests. |[S -> T]| of
\* sizes exceeding Integer.MAX_VALUE are not yet
\* supported.
Init == /\ x \in RandomSubset(1000, [ S -> T ])

Next == /\ UNCHANGED <<x>>

Spec == Init /\ [][Next]_<<x>>

Inv == TRUE
=============================================================================
