------------------------------- MODULE Github1485Case --------------------------------
\* Regression spec for https://github.com/tlaplus/tlaplus/issues/1485.
\*
\* A next-state relation whose top-level operator is CASE used to be rejected
\* by -generate ("Probabilistic evaluation of next-state relation not
\* implemented for CASE yet").  With uniform successor selection evaluating
\* the complete next-state relation, CASE requires no special treatment
\* anymore.  (As in breadth-first mode, TLC takes the first CASE arm whose
\* guard is true.)

EXTENDS Naturals

VARIABLE x

vars == <<x>>

Init == x = 0

Next ==
    CASE x >= 0 -> x' = 0
      [] x >= 0 -> x' = 1

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Created Mon Oct 24 2026
