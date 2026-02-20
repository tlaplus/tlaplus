---------------------------- MODULE Github1244 ----------------------------
VARIABLE x
vars == <<x>>
Init == x = FALSE
Next == x' = ~x

MyInit(myInit) == myInit                       \* state-level
Spec ==
  /\ MyInit(Init)
  /\ [][Next]_vars

MyAction(myAction) == myAction                 \* action-level
SpecAction ==
  /\ Init
  /\ [][MyAction(Next)]_vars

MyNext(myNext) == myNext                       \* temporal-level
SpecNext ==
  /\ Init
  /\ MyNext([][Next]_vars)
===========================================================================

---------------------------- CONFIG Github1244 ----------------------------
SPECIFICATION Spec
===========================================================================
