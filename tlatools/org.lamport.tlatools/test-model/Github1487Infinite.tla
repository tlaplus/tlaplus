------------------------- MODULE Github1487Infinite -------------------------
EXTENDS Integers

VARIABLES nat, sub, fcn, pred, i, k

\* Infinite values, which TLC cannot fingerprint. Without a VIEW, TLC thus
\* rejects the initial states.
Init == /\ nat = Nat
        /\ sub = SUBSET Nat
        /\ fcn = [n \in Nat |-> n]
        /\ pred = {n \in Nat : n > 0}
        /\ i = 0
        /\ k \in 1..64

Next == /\ i < 3
        /\ i' = i + 1
        /\ UNCHANGED <<nat, sub, fcn, pred, k>>

\* The view does not fingerprint the infinite values.
View == <<i, k>>

\* Membership and function application do not enumerate the infinite values.
Inv == /\ 1 \in nat /\ -1 \notin nat
       /\ {0, 1} \in sub /\ {-1} \notin sub
       /\ fcn[42] = 42
       /\ 1 \in pred /\ 0 \notin pred
=============================================================================
