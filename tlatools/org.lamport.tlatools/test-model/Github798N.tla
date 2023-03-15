---------------------------- MODULE Github798N ---------------------------
S == {"n1", "n2"}

Direct(xx, yy) ==
    /\ xx \in [S -> {"a"}]
    /\ yy \in [S -> S]
    /\ \A s \in S : 
        xx[s] = "a" => yy[s] = s

Indirect(xx, yy) == 
    /\ Direct(xx, yy)

InIndirect(xx, yy) ==
	LET zz == xx IN
    Indirect(zz, yy)

VARIABLE x, y

vars == <<x, y>>

Init == 
	/\ x = {}
	/\ y = {}

Next ==
    InIndirect(x', y')
   
Spec == 
    Init /\ [][Next]_vars

==========================================================================
---------------------------- CONFIG Github798N ----------------------------
SPECIFICATION
    Spec
===========================================================================
