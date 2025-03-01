Label parameters are required if labels occur within the scope of bound
identifiers, but these parameters should obey common-sense restrictions like
not defining the same parameter twice.
---- MODULE E2033_Quantifier_Test ----
op == \A x \in {} : lbl(x, x) :: 0
====

