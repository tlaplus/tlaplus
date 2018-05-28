------------------------------- MODULE test57a ------------------------------
\* Test of subtle INSTANCE semantics
EXTENDS Naturals
VARIABLES u, v
A == (u'=u) /\ (v'=v+1)
B(d) == ENABLED d
C == B(A)
D == ENABLED A
=============================================================================