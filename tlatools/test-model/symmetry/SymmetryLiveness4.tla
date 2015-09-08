------------------------- MODULE SymmetryLiveness3 -------------------------
EXTENDS Integers
CONSTANT S
Other(n) == CHOOSE x \in S \ {n} : TRUE

VARIABLES x, y

Init == x \in S /\ y = 0

\* MCa (SymmetryModelCheckerTest3a)
N1 ==   \/ /\ y = 0
           /\ y' = 1
           /\ x' = x
        \/ /\ y = 1
           /\ y' = 0
           /\ x' = Other(x)
Spec1 == Init /\ [][N1]_<<x, y>> /\ WF_<<x,y>>(N1) \* Violates Prop1, but TLC produces bogus trace

\* MC (SymmetryModelCheckerTest3)
\* Contrary to N1, x' either stays unchanged OR assumes Other(x)
N2 ==   \/ /\ y = 0
           /\ y' = 1
           /\ x' = x
        \/ /\ y = 1
           /\ y' = 0
           /\ x' = x
        \/ /\ y = 1
           /\ y' = 0
           /\ x' = Other(x)
Spec2 == Init /\ [][N2]_<<x, y>> /\ WF_<<x,y>>(N2) \* Fails to find error in Prop1

\*Prop1 == []<>[](x \notin S)
\*Prop1==[]<>[](y=0)
\*[](Cardinality of S is two)
\*Prop1 == <>[](y=0 ~> y=1)
Prop1 == <>[][x'=x]_<<x, y>>
\*Prop1 == (y=0 ~> y=0) /\ (<>[][x'=x]_<<x, y>>)
\*Prop1 == (x \in S ~> x \in (S \ {Other(x)}))
=============================================================================
