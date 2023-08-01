---- MODULE CyclicRedefineInstance ----
EXTENDS Base

ReDefNext ==
	LET B == INSTANCE Base
	IN \/ B!Next
	   \/ x' = TRUE
=====
----- MODULE Base -----
VARIABLE x

Next ==
    x' = FALSE

Spec ==
	x = FALSE /\ [][Next]_x

Inv ==
	x = FALSE
====
