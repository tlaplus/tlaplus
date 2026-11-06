------------------------------ MODULE Github1485ConjTRUE ------------------------------
\* Regression spec for https://github.com/tlaplus/tlaplus/issues/1485.
\*
\* Semantically equivalent to Github1485Disj, but because the next-state
\* relation is a conjunction at the top level, TLC cannot split Next into the
\* sub-actions A and B and evaluates the complete disjunction inside the
\* next-state relation instead.  With uniform successor selection, the
\* distribution over the five successor states x' \in 0..4 is identical to
\* Github1485Disj: each one is selected with probability 1/5.

EXTENDS Naturals

VARIABLE x

vars == <<x>>

Init == x = 0

A ==
    /\ \E i \in 0..3 : x' = i
    /\ x < 100

B == x' = 4

Next == (A \/ B) /\ TRUE

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Created Mon Oct 24 2026
