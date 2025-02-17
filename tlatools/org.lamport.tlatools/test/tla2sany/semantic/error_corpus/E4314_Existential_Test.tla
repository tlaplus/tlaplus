If an existential quantifier has a temporal-level body, it cannot have an
action-level set bound.
---- MODULE E4314_Existential_Test ----
VARIABLE v
op == \E x \in v' : []v
====

