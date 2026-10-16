---- MODULE Github763 ----

CONSTANT MV
VARIABLE x
Init == x = {}
Grow == x' = [val |-> 1]
Next == Grow \/ UNCHANGED x
Spec == Init /\ [][Next]_x /\ WF_<<x>>(Grow)
Live == []<>(x /= MV)

====
---- CONFIG Github763 ----
SPECIFICATION Spec
CONSTANT MV = MV
PROPERTY Live
====
