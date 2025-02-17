Label parameters are required if labels occur within the scope of bound
identifiers, but not identifiers introduced by operators.
---- MODULE E4332_Set_Test ----
op(x) == {y \in {} : lbl(x, y) :: TRUE}
====

