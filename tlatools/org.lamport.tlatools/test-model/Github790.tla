---- MODULE Github790 ----
VARIABLE a
Init == a = 0
Next == UNCHANGED a
Spec == Init /\ [][Next]_a
AlwaysTrue == <>TRUE => <>[]TRUE
====
---- MODULE Github790_proof ----
EXTENDS Github790, TLAPS

THEOREM AlwaysTrue
BY PTL DEF AlwaysTrue
====

