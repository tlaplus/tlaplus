-------------------- MODULE test202 ----------------
\* Test of recursion

EXTENDS Naturals, TLC

RECURSIVE g(_)
f(a) == IF a = 0 THEN 1 ELSE a * g(a-1)
g(a) == f(a) 


ASSUME /\ f(0) = 1
       /\ f(4) = 24
       /\ \A i \in 1..5 : f(i) = i * f(i-1)
       /\ PrintT("Test 1 OK")

ASSUME /\ g(0) = 1
       /\ g(4) = 24
       /\ \A i \in 1..5 : g(i) = i * g(i-1)
       /\ PrintT("Test 2 OK")

RECURSIVE fact
fact1[n \in Nat] == fact[n]
fact[n \in Nat] == IF n = 0 THEN 1 ELSE n * fact1[n-1]

ASSUME /\ fact1[3] = 6
       /\ fact[4] = 24
       /\ \A i \in 0..5 : fact[i] = g(i)     
       /\ PrintT("Test 3 OK")


=================================================

