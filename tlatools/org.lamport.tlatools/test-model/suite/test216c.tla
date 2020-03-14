------------------ MODULE test216c ---------------------
EXTENDS Naturals
VARIABLE x

InitC == x = 0
NextC == x'=(x+1) %6

SpecC == [][NextC]_x

THEOREM ThmC == SpecC => [](x \in Nat)

THEOREM ThmC2 == [](x \in Nat)

THEOREM ThmC3 == 1+1 = 2
======================================================