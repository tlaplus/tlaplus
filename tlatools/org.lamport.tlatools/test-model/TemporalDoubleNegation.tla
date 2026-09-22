---- MODULE TemporalDoubleNegation ----
EXTENDS Integers

\* Regression cases for https://github.com/tlaplus/model-checker-hardening/issues/183
VARIABLE x

Init == x = 0
Next == (x < 3 /\ x' = x + 1) \/ UNCHANGED x
Spec == Init /\ [][Next]_x
FairSpec == Spec /\ WF_x(Next)

\* Every behavior of Spec satisfies these six properties, since x >= 0 is
\* invariant. ImplicationTautology is valid independently of Spec.
AlwaysDoubleNegation == [](~(~([](x >= 0))))
AlwaysDual == ~(<>(~([](x >= 0))))
EventuallyDoubleNegation == <>(~(~([](x >= 0))))
ImplicationDoubleNegation == [](x >= 0 => ~(~([](x >= 0))))
ImplicationTautology == <>(~(FALSE ~> FALSE)) => FALSE
LeadsToDual == ~(<>(~(x >= 0 ~> x >= 0)))

\* These require FairSpec: weak fairness forces x to reach 3 and stay there.
\* Spec alone admits the counterexample that stutters forever at x = 0.
FairEventuallyDoubleNegation == <>(~(~([](x = 3))))
FairLeadsToDual == ~(<>(~(x = 0 ~> x = 3)))
====
