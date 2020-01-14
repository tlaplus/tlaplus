------------------------------ MODULE L ------------------------------
EXTENDS Naturals

VARIABLE v

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y)

Spec == v = ChooseOne({1}, LAMBDA x : TRUE) /\ [][UNCHANGED v]_v

============
