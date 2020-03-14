--------------- MODULE test19 -------------

(* Test of large initial state space *)

EXTENDS Naturals, Sequences

VARIABLE x, y, z 
Init == /\ x \in 1..100
        /\ y \in 1..200
        /\ z \in 1..20

Next == UNCHANGED <<x, y, z>>

Inv == TRUE
=========================================
