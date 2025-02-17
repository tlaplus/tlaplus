Label parameters are required if labels occur within the scope of bound
identifiers, but not identifiers introduced by operators.
---- MODULE E4332_Quantifier_Test ----
op(x) == \A y \in {} : lbl(x, y) :: TRUE
====

