---- MODULE Github1037 ----
EXTENDS Naturals
VARIABLE x
Init == x = 1
Next ==
  IF x = 5 THEN UNCHANGED x
  ELSE x' = x + 1
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Liveness == (x = 1) => <>[](x = 5)
=====
----- CONFIG Github1037 -----
SPECIFICATION Spec
PROPERTY Liveness
=====