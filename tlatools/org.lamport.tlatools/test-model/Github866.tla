---------------------------- MODULE Github866 ---------------------------
EXTENDS Naturals, TLC, FiniteSets
VARIABLES x
vars == << x >>

X == {RandomElement({1,2,3})}

Init == x = 0
Lbl_1 == /\ x < 50 \* Generate some states to ensure both workers have work to do.
         /\ TLCSet(42, X)
         /\ x' = x + 1

Next == Lbl_1

Spec == Init /\ [][Next]_vars

==========================================================================
---------------------------- CONFIG Github866 ----------------------------
SPECIFICATION Spec
=============================