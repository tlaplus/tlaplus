The @ symbol has special syntactic meaning and cannot be used as an
ordinary declared identifier, so it cannot be bound in a set comprehension.
---- MODULE E4261_SubsetOf_Test ----
op == {@ \in {0} : TRUE}
====
