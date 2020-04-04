----------------------------- MODULE April20a -----------------------------
EXTENDS Integers

CONSTANT S

VARIABLE x, y
vars == <<x, y>>

Init == (x = 0) /\ (y=0)

Next == \/ /\ y=0
           /\ y'=1
           /\ x' \in S
        \/ /\ y=1
           /\ y'=2
           /\ x' \in S \ {x} 
        \/ /\ y = 2
           /\ y'=0
           /\ x' = 0

Spec == Init /\ [][Next]_vars

Live == ~ \A i \in S : \E j \in S \ {i} : []<><<x'=i /\ x=j>>_x
=============================================================================
