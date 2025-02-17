When introducing a new constant in an ASSUME/PROVE block, if a set bound is
given then that set bound cannot be of temporal level.
---- MODULE E4356_Test ----
VARIABLE v
THEOREM
  ASSUME NEW x \in []v
  PROVE TRUE
====

