---------------------------- MODULE Github1394 ----------------------------
EXTENDS Naturals, Github1394Base

vars == <<x>>
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == x \in 0..2

THEOREM BoxTypeOK == []TypeOK
THEOREM BoxSmall == [](x < 2)
THEOREM SpecTypeOK == Spec => []TypeOK
THEOREM SpecSmall == Spec => [](x < 2)
THEOREM SpecReachesTwo == Spec => <>(x = 2)
THEOREM SpecReachesFive == Spec => <>(x = 5)
THEOREM StateInv == x \in 0..2
LEMMA Small == x < 2

Props == BoxTypeOK /\ []StateInv
===========================================================================
