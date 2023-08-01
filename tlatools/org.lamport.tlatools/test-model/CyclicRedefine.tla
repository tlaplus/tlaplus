---- MODULE CyclicRedefine ----
EXTENDS Base, TLC

ReDefInit ==
    /\ x \in BOOLEAN
    /\ Init

ReDefNext ==
    Next /\ ~A(1)

ReDefA(n) ==
    /\ x' = Print(<<"ReDef", n>>, FALSE)
    /\ A(n)

YetAnotherOp(s, b, P(_)) ==
	Print("ReDefOp", P(b))

ReDefOp(b) ==
    YetAnotherOp("ReDefOp", b, Op)
	
ReDefInv ==
	Inv /\ x = FALSE
=====
----- MODULE Base -----
VARIABLE x

Init == x = FALSE                      \* line  4

Op(b) == ~b                            \* line  6

A(n)== x' = Op(FALSE)                  \* line  8

B== x' = FALSE                         \* line 10

Next == \E i \in {1,2,3}: A(i) \/ B    \* line 12

Inv ==
	x \in BOOLEAN

====
