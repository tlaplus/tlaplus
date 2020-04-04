-------------------- MODULE test203 ----------------
\* Test of recursion

EXTENDS Naturals, TLC

RECURSIVE g(_)

foo(n) == INSTANCE test203a WITH A <- g, b <- n

g(n) == IF n = 0 THEN 1 ELSE n * foo(n-1)!h

ASSUME /\ g(0) = 1
       /\ g(4) = 24
       /\ \A i \in 1..5 : g(i) = i * g(i-1)
       /\ PrintT("Test1 OK")
=================================================

