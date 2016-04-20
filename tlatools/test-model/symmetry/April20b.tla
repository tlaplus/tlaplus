----------------------------- MODULE April20b -----------------------------
EXTENDS Integers, Sequences

CONSTANT S

VARIABLE x, y
vars == <<x, y>>

Init == (x = << >>) /\ (y=0)

Next == \/ /\ y=0
           /\ y'=1
           /\ \E s \in S : x' = <<s>>
        \/ /\ y=1
           /\ y'=2
           /\ \E s \in S \ {x[1]} : x' = Append(x, s) 
        \/ /\ y = 2
           /\ y'=0
           /\ x' = << >>

Spec == Init /\ [][Next]_vars

Live == ~ \A i \in S : \E j \in S \ {i} : []<>(x = <<i, j>>)
=============================================================================
