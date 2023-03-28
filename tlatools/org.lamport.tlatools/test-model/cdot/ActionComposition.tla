------ MODULE ActionComposition ------
EXTENDS Naturals

VARIABLE x

Init ==
    x = 0

A ==
    \/ /\ x  \in {0}
       /\ x' \in {1, 2, 3}
    \/ /\ x  \in {4}
       /\ x' \in {5}

B ==
    \/ /\ x  \in {1, 2}
       /\ x' \in {2, 4}
    \/ /\ x  \in {5}
       /\ x' \in {6}

Next ==
    A \cdot B

Spec ==
    Init /\ [][Next]_x

Inv ==
    x \in {0, 1, 2, 4, 6}

Inv2 ==
	x < 3 \/ ENABLED Next

Prop ==
	[][~(B \cdot A)]_x

Prop2 ==
	[][Next]_x

ActionConstraint ==
    <<Next>>_x
======
