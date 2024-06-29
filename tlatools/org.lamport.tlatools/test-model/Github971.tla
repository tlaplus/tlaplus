---- MODULE Github971 ----
EXTENDS Integers

VARIABLE x

InitA ==
    x = 0

InitB ==
    x = -1

NextAB ==
    x' \in {0,1} 

NextC ==
    NextAB \/ x' = 2

AtMostOnce ==
    []((x=1) => []((x=0) => [](x=0)))

AtMostOnceC ==
    []((x=1) => []((x=0) => [](x=2)))
==========================

fp(x =-1) =  3234510876920644087
fp(x = 0) = -3406341414084290173
fp(x = 1) =  -686636423115914061
fp(x = 2) = -7115858903467826205