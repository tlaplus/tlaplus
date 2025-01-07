---------------------------- MODULE Github1109 ---------------------------
EXTENDS Sequences

Part_Funct(D, R) == UNION {[d -> R] : d \in SUBSET D}

S == {"s"}

R == Seq(S) \* Cannot be enumerated.

CONSTANTS C

ASSUME DOMAIN C # {} \* Evaluate C to trigger Seq(S).

C2 == [ s \in [S -> R], p \in {Part_Funct(S, R)} |-> TRUE ]
==========================================================================
---------------------------- CONFIG Github1109 ---------------------------
CONSTANT C <- C2
==========================================================================
