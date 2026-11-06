------------------------------- MODULE Github1485Disj -------------------------------
\* Regression spec for https://github.com/tlaplus/tlaplus/issues/1485.
\*
\* TLC splits the next-state relation into the two actions A and B of which
\* both are enabled in the (single) initial state x = 0.  A has the four
\* successor states x' \in 0..3 (one per binding of \E i \in 0..3) and B has
\* the single successor state x' = 4.  With uniform successor selection, each
\* of the five successor states is selected with probability 1/5.  The
\* previous, first-found selection instead picked one of the successor states
\* of whichever action happened to come first in the traversal order.

EXTENDS Naturals

VARIABLE x

vars == <<x>>

Init == x = 0

A ==
    /\ \E i \in 0..3 : x' = i
    /\ x < 100

B == x' = 4

Next == A \/ B

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Created Mon Oct 24 2026
