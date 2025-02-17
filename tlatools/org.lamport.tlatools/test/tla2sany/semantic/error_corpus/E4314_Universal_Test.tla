If a universal quantifier has a temporal-level body, it cannot have an
action-level set bound.
---- MODULE E4314_Universal_Test ----
VARIABLE v
op == \A x \in v' : []v
====

