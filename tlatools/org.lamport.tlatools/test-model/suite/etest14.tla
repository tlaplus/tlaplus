----------------------  MODULE etest14 -----------------------------

\* Test of CHOOSEing element of empty set.
ASSUME
  /\ (CHOOSE y \in {} : TRUE) = (CHOOSE y \in {} : TRUE)
=====================================================================
