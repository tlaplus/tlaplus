---- MODULE Github1037 ----
EXTENDS Naturals
VARIABLE x
Init == x = 1
Next ==
  /\ x < 3
  /\ x' = x + 1
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Liveness == (x = 1) => <>[](x = 3)
=====
----- CONFIG Github1037 -----
SPECIFICATION Spec
PROPERTY Liveness
=====