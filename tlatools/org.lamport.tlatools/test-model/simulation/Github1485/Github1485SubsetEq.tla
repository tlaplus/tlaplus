---- MODULE Github1485SubsetEq ----
EXTENDS Naturals
VARIABLE x
Init == x = {}
Next == x' \subseteq (1..20)
====
