Labels are not permitted within function-except clauses.
---- MODULE E4335_Test ----
f[x \in {}] == x
op == [f EXCEPT ![0] = lbl :: 0]
====

