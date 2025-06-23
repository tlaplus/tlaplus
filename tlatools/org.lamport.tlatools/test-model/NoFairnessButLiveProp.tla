---- MODULE NoFairnessButLiveProp ----

VARIABLE b

Init ==
    b = FALSE

Next ==
    b' = TRUE

SpecNoFair ==
    Init /\ [][Next]_b

SpecWithFair ==
    Init /\ [][Next]_b /\ WF_b(Next)

------

Live ==
    WF_b(Next)

------

H == INSTANCE H

RefinementNoFair ==
    H!SpecNoFair

RefinementWithFair ==
    H!SpecWithFair

=============================================================================
---- MODULE H ----

VARIABLE b

SpecNoFair ==
    b \in BOOLEAN /\ [][b' \in BOOLEAN]_b

SpecWithFair ==
    b \in BOOLEAN /\ [][b' \in BOOLEAN]_b /\ WF_b(b' \in BOOLEAN)
=============================================================================
