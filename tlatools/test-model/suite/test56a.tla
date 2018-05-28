------------------------------- MODULE test56a ------------------------------
\* Test of subtle INSTANCE semantics
EXTENDS Naturals
VARIABLE u
G(v, A) == ENABLED (A \/ (u'=u /\ v'=v) \/ (v'=u /\ u'=v))
H == (u'=u) /\ G(u, u' = u + 1)
=============================================================================