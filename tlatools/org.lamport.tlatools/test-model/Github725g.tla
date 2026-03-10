---- MODULE Github725g ----
EXTENDS Naturals

VARIABLES b, q, s

Svc == INSTANCE Inner725g WITH c <- s,
\* The inner module has a variable named b and
\* the outer module also has a variable named b.
a <- b , b <- q

Init == /\ b = 0
        /\ q = 0
        /\ s = << 1, 2, 3 >>

Next == UNCHANGED << b, q, s >>

Spec == /\ Init
        /\ [][Next]_<< b, q, s >>
        \* Fairness is defined in the inner module.
        /\ Svc!Fairness

\* Github725gTest (liveness, soundness): The false ENABLED=TRUE strengthens
\* WF_vars(Step), eliminating all valid behaviors and making <>(b=1)
\* vacuously satisfied. TLC reports success, missing a temporal property
\* violation on the stuttering behavior.
Prop == <>( b = 1 )

\* Github725hTest (safety, soundness): The invariant IF Svc!StepEnabled THEN TRUE
\* ELSE b /= 0 evaluates ENABLED through the inner module's definition
\* (Svc!StepEnabled), where eval's SubstInNode handling adds the INSTANCE
\* substitutions to the context before OPCODE_enabled branches it — the
\* same broken Context layout as the liveness case. TLC reports success,
\* missing an initial-state invariant violation.
Inv == IF Svc!StepEnabled THEN TRUE ELSE b /= 0

====

---- MODULE Inner725g ----
EXTENDS Sequences, Naturals

VARIABLES a, b, c
vars == << a, b, c >>

NoOverrideSelectSeq(s, Test(_)) ==
  LET F[i \in 0 .. Len(s)] ==
        IF i = 0
        THEN <<>>
        ELSE IF Test(s[i]) THEN Append(F[i - 1], s[i]) ELSE F[i - 1]
  IN F[Len(s)]

\* Replacing SelectSeq with the pure TLA+ implementation
\* NoOverrideSelectSeq causes TLC to correctly report both violations,
\* confirming the bug is in the Java override's LAMBDA evaluation path.
Step == /\ a = 0
        /\ b' = 42
        /\ a' = 1
        \* The following two conjuncts equal false. TLC correctly reports
        \* a counterexample when SelectSeq is replaced with NoOverrideSelectSeq.
        /\ c' = SelectSeq(c, LAMBDA e:e /= a')
        /\ c' = << 1, 2, 3 >>

Fairness == WF_vars(Step)

StepEnabled == ENABLED Step

====
