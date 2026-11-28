---- MODULE Github1485SubsetBinding ----
EXTENDS Naturals
VARIABLE x
Init == x = {}
Next == (\E y \in SUBSET (1..20) : x' = y) /\ TRUE
====
