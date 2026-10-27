---- MODULE Github1497 ----
VARIABLE x

Init == x = 0
Next == x' = 1

Spec == Init /\ [][Next]_x

Prop == <>[](x = 0)
====
