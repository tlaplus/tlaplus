---- MODULE CyclicRedefineVars ----
EXTENDS Base, TLC

VARIABLE z

ReDefInit ==
    /\ x \in BOOLEAN
    /\ z = TRUE
    /\ Init

ReDefA(n) ==
    /\ A(n)
	/\ z' = ~z

ReDefB ==
	/\ B
	/\ z' = ~z

ReDefVars ==
	<<vars, z>>

=====
----- MODULE Base -----
VARIABLE x

vars == <<x>>

Init == x = FALSE

Op(b) == ~b

A(n)== x' = Op(FALSE)

B == x' = FALSE

Next == \E i \in {1,2,3}: A(i) \/ B

Spec ==
	Init /\ [][Next]_vars

Inv ==
	x \in BOOLEAN

====
