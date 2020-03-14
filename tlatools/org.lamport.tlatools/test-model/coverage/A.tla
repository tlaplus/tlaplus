---------------------------- MODULE A ----------------------------
EXTENDS Naturals, FiniteSets
VARIABLE x

Op1(S) == \A e \in SUBSET S : Cardinality(e) >= 0

Init == /\ x = 0
        /\ Op1(1..17)

\* Max(s)
Op2(n) == CHOOSE i \in 1..n : \A j \in ((1..n) \ {i}) : i > j

A(n) == x' = Op2(n)

B(n) == x' = Op2(n)

Next == A(10) \/ B(3)
=============================================================================
