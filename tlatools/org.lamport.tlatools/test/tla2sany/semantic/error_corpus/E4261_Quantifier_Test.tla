The @ symbol has special syntactic meaning and cannot be used as an
ordinary declared identifier, so it cannot be bound by a quantifier.
---- MODULE E4261_Quantifier_Test ----
op == \E @ \in {0} : TRUE
====
