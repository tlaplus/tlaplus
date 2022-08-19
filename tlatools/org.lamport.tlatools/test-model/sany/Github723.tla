---- MODULE Github723 ----
\* https://github.com/tlaplus/tlaplus/issues/723

EXTENDS Naturals

---- MODULE Inner ----
CONSTANT C(_)

D(x) == C(x)
====

C(x, y) == x

INSTANCE Inner

VARIABLE x
Spec == x = 0 /\ [][x' = D(x)]_x
Inv == x = 0

====
