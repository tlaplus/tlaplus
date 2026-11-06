--------------------------- MODULE Github1485BoundedExists ---------------------------
\* Regression spec for https://github.com/tlaplus/tlaplus/issues/1485.
\*
\* The next-state relation is a single action with an existentially quantified
\* variable of which the bindings i = 0 and i = 1 are enabled in the (single)
\* initial state x = 0.  A successor state of the initial state is therefore
\* x = 0 or x = 1; with uniform successor selection, both are equally likely,
\* i.e. P(x' = 0) = P(x' = 1) = 1/2.

EXTENDS Naturals

VARIABLE x

vars == <<x>>

Init == x = 0

Next ==
    \E i \in {0, 1, 2} :
        /\ i < 2
        /\ x' = i

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Created Mon Oct 24 2026
