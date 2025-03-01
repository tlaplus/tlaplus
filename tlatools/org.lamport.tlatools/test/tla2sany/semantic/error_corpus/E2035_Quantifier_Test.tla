Label parameters are required if labels occur within the scope of bound
identifiers, but not identifiers introduced by operators.
---- MODULE E2035_Quantifier_Test ----
op(x) == \A y \in {} : lbl(x, y) :: 0
====

