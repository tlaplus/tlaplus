---- MODULE DiffTraceAlias ----
EXTENDS DiffTrace, Naturals

\* ab is not a variable.
Alias == [a |-> a, b |-> b, c |-> c, d |-> d, ab |-> a + b]

\* a changes from a string to an integer, and once c = 1 the alias is not a
\* record, so TLC prints the state itself.
MixedAlias == IF c = 0 THEN [a |-> IF a = 0 THEN "none" ELSE a, ab |-> a * b] ELSE c

\* Fails for every state, so TLC prints the state with an _ALIASEvalError field.
FailingAlias == [a |-> a, q |-> a \div (d - d)]

\* Fair behaviors take all four steps and then stutter with d = 1, which
\* violates Liveness.
Spec == Init /\ [][Next]_<<a, b, c, d>> /\ WF_<<a, b, c, d>>(Next)

Liveness == []<>(d = 0)
====
