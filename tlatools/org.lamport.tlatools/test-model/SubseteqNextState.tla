---- MODULE SubseteqNextState ----
VARIABLE x
TypeOK == x \subseteq {1, 2, 3}
Inv == ENABLED (x' \subseteq {1})
Init == x \subseteq {1, 2}
Next == x' \subseteq {1, 2, 3}
====
