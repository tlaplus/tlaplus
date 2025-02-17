When introducing a new constant in an ASSUME/PROVE block, if a set bound is
given then that set bound cannot be of temporal level.
---- MODULE E2027_Test ----
THEOREM
  ASSUME NEW x \in []0
  PROVE TRUE
====

