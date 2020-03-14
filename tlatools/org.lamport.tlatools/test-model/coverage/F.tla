---------------------------- MODULE F ----------------------------
EXTENDS Naturals

VARIABLE x

Op(S, P(_), Q(_, _)) == { s \in S : P(s) /\ Q(s, TRUE) }

Init == x \in Op({1,2,3,4,5}, LAMBDA s: s > 1, LAMBDA odd, b: odd % 2 # 0 /\ b) 

Next == UNCHANGED x
=============================================================================
