It is an error to use labels in inner nested ASSUME/PROVE blocks when that
block also introduces a new symbol using a NEW statement. Why this is the
case for nested ASSUME/PROVE blocks but not top-level ones is unknown.
---- MODULE E4334_Test ----
THEOREM thm ==
  ASSUME
    ASSUME
      NEW x \in {},
      lbl :: TRUE
    PROVE TRUE
  PROVE TRUE
====

