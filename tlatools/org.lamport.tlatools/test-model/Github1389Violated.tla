--------------------------- MODULE Github1389Violated ---------------------------
\* Counterexample counterpart of Github1389.tla
\* (see https://github.com/tlaplus/tlaplus/issues/1389).
\*
\* Github1389.tla exercises the positive case: a RECURSIVE operator that
\* produces a temporal formula which holds.  This module exercises the
\* inverse: the expanded property is genuinely violated, and TLC must
\* yield a counterexample rather than emit TLC_LIVE_CANNOT_HANDLE_FORMULA
\* or misclassify the failure.

EXTENDS Naturals

VARIABLE x

\* PropViolated reduces during tableau construction (via expansion and
\* the constant-guard handling of OPCODE_ite) to <>(x = 99).  Since x
\* toggles deterministically over {0, 1}, no reachable behavior ever has
\* x = 99, so the property fails.  <> (rather than []) is used so
\* SpecProcessor cannot route the formula to invariant checking; it must
\* flow through the liveness tableau and surface as
\* TLC_TEMPORAL_PROPERTY_VIOLATED.  WF_x(Next) forces progress so the
\* counterexample is the deterministic two-state cycle 0 -> 1 -> 0
\* rather than a trivial stuttering trace.
RECURSIVE Reach(_)
Reach(n) == IF n = 0 THEN <>(x = 99) ELSE Reach(n - 1)

Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)

PropViolated == Reach(3)
==================================================================
