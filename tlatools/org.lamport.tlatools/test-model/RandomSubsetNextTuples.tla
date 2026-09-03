---------------------- MODULE RandomSubsetNextTuples ----------------------
EXTENDS Integers, Randomization

VARIABLE p, q, y

\* Not two more variables of RandomSubsetNext.tla, where a freshly drawn tuple
\* all but never repeats an earlier one, so nothing bounds a level the way
\* x \in 1..1000 does and its ten successors per state put 10^9 states below
\* y = 10.

\* Product has fewer elements than an int holds and BigProduct more.
Product == (1..200) \X (1..200) \X (1..200)
BigProduct == (1..4000) \X (1..4000) \X (1..4000)

Init == /\ p \in RandomSubset(2, Product)
        /\ q \in RandomSubset(2, BigProduct)
        /\ y = 0

Next == /\ p' \in RandomSubset(2, Product)
        /\ q' \in RandomSubset(2, BigProduct)
        /\ y' = y + 1

Spec == Init /\ [][Next]_<<p,q,y>>

\* Four successors per state, i.e. 4^y states of level y.
Inv == y < 6

TypeOK == /\ y \in Nat
          /\ p \in Product
          /\ q \in BigProduct
=============================================================================
