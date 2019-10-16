---- MODULE Github377 ----

VARIABLES x

Spec == x = TRUE /\ [][UNCHANGED x]_x

--------------

1Inv ==
 LET recfcn[ i \in {1,2,3} ] == IF i = 1 THEN x = TRUE ELSE recfcn[1]
 IN recfcn[1]
 
=====