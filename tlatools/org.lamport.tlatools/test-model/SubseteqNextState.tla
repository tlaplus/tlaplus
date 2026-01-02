---- MODULE SubseteqNextState ----
VARIABLES x, y
TypeOK == x \subseteq {1, 2, 3}
Inv ==
  /\ ENABLED (x' \subseteq {1})
  /\ y = {1, 2, 3}
Init ==
  /\ x \subseteq {1, 2}
  /\ y = {1, 2, 3}
Next ==
  /\ UNCHANGED y
  /\ x' \subseteq y'
====
