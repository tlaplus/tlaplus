--------------------------- MODULE AssignmentInit ---------------------------
EXTENDS Integers
VARIABLE s

min(S) == CHOOSE e \in S: \A a \in S: e <= a

InitExit(var, S) == \E val \in S: (var = val /\ var > min(S))

InitAll(var, S) == \A val \in S: (var = val /\ var \in S)

InitIn(var, S) == var \in S /\ var > min(S)

\* With this Init(var), the test does not fail without its fix.
\*Init(ignored) == \E val \in {0,1}: (s = val /\ s > 0)

\* Init1 one state + Init3 one state
Spec == /\ \/ InitExit(s, {0,1}) \* 1 unique state
           \/ InitAll(s, {2})    \* 1 unique state
           \/ InitIn(s, {4,5})   \* 1 unique state
           \/ InitAll(s, {6,7})  \* 0 unique states
        /\ [][UNCHANGED s]_s

=============================================================================
