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

SpecWithCustomFair ==
    Init /\ [][Next]_b /\ <>(b = TRUE)

------

Live ==
    WF_b(Next)

SafetyProp ==
    [](b => [](~b => []~b))

EventuallyB ==
    <>(b = TRUE)

LeadsToB ==
    (b = FALSE) ~> (b = TRUE)

InfOftenB ==
    []<>(b = TRUE)

EventuallyAlwaysB ==
    <>[](b = TRUE)

VacuousLive ==
    (b = TRUE) => <>(b = FALSE)

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
