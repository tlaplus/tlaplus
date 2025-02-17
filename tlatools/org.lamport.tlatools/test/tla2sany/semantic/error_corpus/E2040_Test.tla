Labels are not permitted within function-except clauses.
---- MODULE E2040_Test ----
op == [TRUE EXCEPT ![0] = lbl :: 0]
====

