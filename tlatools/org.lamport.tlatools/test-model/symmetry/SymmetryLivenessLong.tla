------------------------- MODULE SymmetryLivenessLong -------------------------
EXTENDS Integers
CONSTANT S
Other(n) == CHOOSE x \in S \ {n} : TRUE

VARIABLES x, y

Init == x \in S /\ y = 0

\* Contrary to SymmetryLiveness3, this produces a long trace which results in LiveWorker#bfsPostFix finding a longer path.

\* MCa (SymmetryModelCheckerTestLonga)
N1 ==   \/ /\ y = 0
           /\ y' = 1
           /\ x' = x
        \/ /\ y = 1
           /\ y' = 2
           /\ x' = x
        \/ /\ y = 2
           /\ y' = 3
           /\ x' = x
        \/ /\ y = 3
           /\ y' = 4
           /\ x' = x
        \/ /\ y = 4
           /\ y' = 0
           /\ x' = Other(x)
Spec1 == Init /\ [][N1]_<<x, y>> /\ WF_<<x,y>>(N1) \* Violates Prop1, but TLC produces bogus trace

\* MC (SymmetryModelCheckerTestLong)
\* Contrary to N1, x' either stays unchanged OR assumes Other(x)
N2 ==   \/ /\ y = 0
           /\ y' = 1
           /\ x' = x
        \/ /\ y = 1
           /\ y' = 2
           /\ x' = x
        \/ /\ y = 2
           /\ y' = 3
           /\ x' = x
        \/ /\ y = 3
           /\ y' = 4
           /\ x' = x
        \/ /\ y = 4
           /\ y' = 0
           /\ x' = x
        \/ /\ y = 4
           /\ y' = 0
           /\ x' = Other(x)
Spec2 == Init /\ [][N2]_<<x, y>> /\ WF_<<x,y>>(N2) \* Fails to find error in Prop1


Prop1 == <>[][x'=x]_<<x, y>>
=============================================================================
