---- MODULE Github1198 ----

VARIABLE b

Init ==
    b = FALSE

Next ==
    b' = TRUE

------
\* L equiv F. Warning is raised.

LiveA ==
    WF_b(Next)

SpecA ==
	Init /\ [][Next]_b /\ LiveA

------
\* L equiv F (Conjunction). Warning is raised.

S1B ==
	WF_b(Next)

S2B ==
	S1B

LiveB ==
    /\ S1B
    /\ S2B

SpecB ==
	Init /\ [][Next]_b /\ LiveB

------
\* L equiv F (Quantification). Warning is raised.

LiveC ==
	\A i \in {1,2}: WF_b(Next)

SpecC ==
	Init /\ [][Next]_b /\ LiveC

------
\* F superset of L. Warning is not raised.

LiveD ==
	WF_b(Next)

SpecD ==
	Init /\ [][Next]_b /\ \A i \in {1,2}: LiveD

------
\* L1 /\ L2 equiv F1 /\ F2. Warning should be raised raised. Not supported yet.

LiveE1 ==
	WF_b(Next)

LiveE2 ==
	WF_b(Next)

SpecE ==
	Init /\ [][Next]_b /\ LiveE1 /\ LiveE2

------
\* L superset of F. Warning is not raised.

LiveF1 ==
	WF_b(Next)

LiveF2 ==
	WF_b(Next)

SpecF ==
	Init /\ [][Next]_b /\ LiveF1

------
\* F superset of L. Warning should be raised. Not supported yet.

LiveG1 ==
	WF_b(Next)

SpecG ==
	Init /\ [][Next]_b /\ LiveG1 /\ WF_b(Next)

------

Abstract == 
	INSTANCE Github1198abs

SpecH ==
    Init /\ [][Next]_b
    
Refinement ==
    Abstract!Spec
=============================================================================
