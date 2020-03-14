------------------------------- MODULE test57 -------------------------------
\* Test of subtle INSTANCE semantics
EXTENDS Naturals
VARIABLE x

I == INSTANCE test57a WITH u <- x, v <- x

Init == \E i \in 1..3 : x = i
Next == x' = 9-x
Spec == Init /\ [][Next]_x

Invariant0 == I!B(Next)
Invariant1 == I!C
Invariant2 == ~ I!B(I!A)
Invariant3 == I!D
Property == [][~I!A]_x
=============================================================================
I!C = ENABLED((u'=x) /\ (v' = x+1))
I!B(I!A) = ENABLED ((x'=x) /\ (x'=x+1))

