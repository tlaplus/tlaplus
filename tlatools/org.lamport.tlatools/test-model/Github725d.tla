---- MODULE Github725d ----
VARIABLE a

Init == a = 0

Next == UNCHANGED a

\* LET/IN wrapping a primed variable as the LHS of = inside ENABLED
Inv == ENABLED ((LET y == a' IN y) = 0)
====
