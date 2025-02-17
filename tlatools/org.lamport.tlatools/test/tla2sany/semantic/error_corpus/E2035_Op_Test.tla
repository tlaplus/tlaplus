Label parameters are required if labels occur within the scope of bound
identifiers, but not identifiers introduced by operators.
---- MODULE E2035_Op_Test ----
op(x) == lbl(x) :: 0
====

