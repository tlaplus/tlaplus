-------- MODULE ChainedCdots ---------
EXTENDS Naturals, TLC

ASSUME TLCSet(0, 0)

VARIABLE x

Init ==
    x = 0

A(S) ==
	\E n \in S:
		/\ x' = x + n
		/\ TLCSet(0, TLCGet(0) + x')

Next ==
	/\ x = 0
    /\ A({1,2}) \cdot A({3,4}) \cdot A({5})

Spec ==
    Init /\ [][Next]_x

PostCondition ==
	TLCGet(0) = 63

=======