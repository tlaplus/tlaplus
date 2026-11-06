---- MODULE Github1485Subset ----
EXTENDS Naturals
VARIABLE x
Init == x = {}
Next == x' \in SUBSET (1..20)
====
