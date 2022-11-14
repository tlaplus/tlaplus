---- MODULE CyclicRedefine ----
EXTENDS Base, TLC

ReDefNext ==
    Next /\ ~A

ReDefA ==
    /\ x' = Print("ReDef", FALSE)
    /\ A

ReDefOp(b) ==
	Print("ReDefOp", Op(FALSE))
=====

----- MODULE Base -----
VARIABLE x

Init == x = FALSE     \* line  4

Op(b) == ~b           \* line  6

A== x' = Op(FALSE)    \* line  8

B== x' = FALSE        \* line 10

Next == A \/ B        \* line 12
====
