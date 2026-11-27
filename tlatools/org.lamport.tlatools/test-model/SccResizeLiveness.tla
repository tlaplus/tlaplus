---- MODULE SccResizeLiveness ----
EXTENDS Naturals

VARIABLE x

vars == <<x>>
Init == x = 0
Next == x' = (x + 1) % 96
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
Property == <>[](x # 0)
====
