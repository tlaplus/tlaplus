Label parameters are required if labels occur within the scope of bound
identifiers, but not identifiers introduced by operators. The correct error
should trigger even if the unnecessary parameter coincidentally matches an
existing definition such as a constant or variable.
---- MODULE E4332_Collision_Test ----
CONSTANT x
op == lbl(x) :: 0
====

