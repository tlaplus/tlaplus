---- MODULE Github377 ----
EXTENDS Integers
VARIABLES x

Spec == x = TRUE /\ [][UNCHANGED x]_x

--------------

1Inv ==
 LET recfcn[ i \in {1,2,3} ] == IF i = 1 THEN x = TRUE ELSE recfcn[1]
 IN recfcn[1]

--------------

1InvNonRec ==
 LET recfcn[ i \in {1,2,3} ] == x = TRUE
 IN recfcn[1]

--------------

2Inv ==
  LET outer ==
      LET innerA[ i \in {1} ] == IF i = 1 THEN x = TRUE ELSE innerA[i]
          innerB[ i \in {1} ] == innerA[i] 
      IN innerB[1] /\ 42 = 31 + 11 /\ innerA[1]
  IN  outer

2aInv ==
  LET outer ==
      LET innerA[ i \in {1} ] == IF i = 1 THEN x = TRUE ELSE innerA[i]
          innerB[ i \in {1} ] == innerA[i]
      IN /\ innerA[1]
         /\ innerB[1] 
  IN  outer
  
2bInv ==
  LET outer ==
      LET innerA[ i \in {1} ] == IF i = 1 THEN x = TRUE ELSE innerA[i]
          innerB[ i \in {1} ] == innerA[i]
      IN innerA[1] /\ innerB[1]
  IN  outer
--------------

3aInv ==
  LET outer ==
      LET innerA[ i \in {1} ] == IF i = 1 THEN x = TRUE ELSE innerA[i]
          innerB[ i \in {1} ] == innerA[1]
      IN /\ LET foo(i) == innerA[i]
            IN foo(1)
         /\ innerB[1] 
  IN  outer

--------------

3bInv ==
  LET outer ==
      LET innerA[ i \in {1} ] == IF i = 1 THEN x = TRUE ELSE innerA[i]
          innerB[ i \in {1} ] == innerA[1]
      IN LET foo(i) == innerA[i]
         IN foo(1) /\ innerB[1] 
  IN  outer
  

--------------

4Inv ==
  LET outer ==
      LET inner[ i \in {1} ] ==
          LET innerst[ j \in {1} ] == x = TRUE
          IN  innerst[1]
      IN  inner[1]
  IN  outer
  
====
  