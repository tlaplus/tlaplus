-------------------- MODULE test201 ----------------
\* Test of lambda expressions

EXTENDS Naturals, TLC
Op(A(_)) == A(4)

bar == Op(LAMBDA x : x^2)

ASSUME /\ Op(LAMBDA x : {x,2} ) = {4,2}
       /\ PrintT("Test1 OK")

ASSUME /\ bar = 16 
       /\ PrintT("Test2 OK")

foo == INSTANCE test201a WITH A <- LAMBDA y : y^3, b <- 4

ASSUME /\ foo!def = 64
       /\ PrintT("Test201 OK")
=================================================

