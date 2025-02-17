Some action- and temporal-level operators are non-Leibniz, meaning they fail
to satisfy a substitutivity property that e = f implies F(e) = F(f), for any
expressions e and f; this is because expressions of equal value in one state
can differ in the next state. This lack of substitutivity is one thing that
makes the Temporal Logic of Actions "weird", as Leslie Lamport puts it on
page 70 of *A Science of Concurrent Programs*. See the *TLA+ Version 2: A
Preliminary Guide* for more info & examples on checking operators for the
Leibniz/substitutivity property. Providing non-Leibniz operators as
substitutes for an instantiated module should be an error.
---- MODULE E4244_Always_Test ----
---- MODULE Inner ----
CONSTANT F(_)
====
INSTANCE Inner WITH F <- []
====

