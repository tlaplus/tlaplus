Label parameters are required if labels occur within the scope of bound
identifiers; all bound parameters must be captured and their names must
match. Missing a parameter should be an error.
---- MODULE E4331_Function_Test ----
f[x \in {}] == lbl :: 0
====

