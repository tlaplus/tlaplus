--------------------------- MODULE Github1389Loops ---------------------------
\* Regression test for https://github.com/tlaplus/tlaplus/issues/1389 (and
\* the related stack-overflow described in #720): when a RECURSIVE operator
\* whose body is at temporal level does not terminate during tableau
\* construction, the liveness translator expands it until the JVM raises a
\* StackOverflowError, which TLC.process translates into
\* EC.SYSTEM_STACK_OVERFLOW -- the same path used by every other
\* non-terminating recursion in the codebase.

VARIABLE x

\* The IF guard evaluates to FALSE so the ELSE branch is taken, which
\* always re-invokes `bad` with the same argument; the expanded recursion
\* therefore does not terminate.
RECURSIVE bad(_)
bad(u) == IF u THEN [][TRUE]_x ELSE bad(u)

Spec == x = TRUE /\ [][x' = ~x]_x

\* Pick the FALSE branch so the recursion never reaches the temporal body.
Prop == bad(FALSE)
=============================================================================
