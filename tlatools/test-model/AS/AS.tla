--------------------------------- MODULE AS ---------------------------------
EXTENDS Integers, FiniteSets

CONSTANT c
ASSUME c \in Nat \ {0}

R == -42


VARIABLES x, z

ASTypeOK == /\ x \in 1..c \cup {R}
            /\ z \subseteq 1..c

ASInit == /\ x = R
          /\ z = {}

ASChoose == /\ Cardinality(z) # c 
            /\ \E n \in 1..c \ z : /\ x' = n
                                   /\ z' = z \cup {n}

ASRest == /\ Cardinality(z) = c
          /\ x' = R
          /\ z' = {}

ASNext == ASChoose \/ ASRest

AS == ASInit /\ [][ASNext]_<<x, z>>

=============================================================================
