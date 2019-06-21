------------------------------ MODULE H ------------------------------
EXTENDS Naturals
VARIABLES x

MyNat == 0..30

TypeOK == x \in MyNat

Init == x = 0

A == x' = 23

BandC == \/ /\ x \in MyNat
            /\ x' \in 23..25
         \/ /\ x < 25
            /\ x' = 26

DandE == (x = 23 /\ x' = 42) \/ (x = 123 /\ x' = 4711)

Next == A \/ BandC \/ DandE

Inv == /\ TypeOK
       /\ x = 0

Spec == Inv /\ [][Next]_x

============
