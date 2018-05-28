------------------------------- MODULE test56 -------------------------------
\* Test of subtle INSTANCE semantics
EXTENDS Naturals
VARIABLE x

I == INSTANCE test56a WITH u <- x

NotIBangH == (x'=x) /\ I!G(x, x'=x+1)

Init == \E i \in 1..3 : x = i
Next == x' = 9-x
Spec == Init /\ [][Next]_x

Property == [][I!H = NotIBangH]_x

=============================================================================
I!H = (x'=x) /\ ENABLED (u'=x+1 \/ (u'=x /\ u'=x) \/ (u'=x /\ u'=x))
NotIBangH = (x'=x) /\ ENABLED (x'=x+1 \/ (u'=x /\ x'=x) \/ (u'=x /\ x'=u))
