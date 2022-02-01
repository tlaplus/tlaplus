---- MODULE Github710a ----

VARIABLE x
vars == <<x>>

Init == x = FALSE

Next == x' \in BOOLEAN 

Spec == 
    /\ Init
    /\ [][Next]_vars
    \* /\ WF_x(Next)

StateConstraint ==
    TRUE

\* This is property to check
AtMostOnce == [](x => [](~x => []~x)) \* G(x => G(~x => G~x))

AtMostOnceEquiv == [](~x \/ [](x \/ []~x)) \* G(~x \/ G(x \/ G~x))
====
