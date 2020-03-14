--------------- MODULE etest3  -------------

(* Testing deadlock and number of states found. *)

EXTENDS TLC, Naturals, Sequences, FiniteSets

VARIABLE x, y, z

Init == /\ Print("This test should deadlock after finding two states", TRUE)
        /\ x = {}
        /\ y = {}
        /\ z = 1

Next == /\ x = {}
        /\ x' = {1}        
        /\ y' \in SUBSET x'
        /\ z' = z
        /\ y' = {}

Inv ==  TRUE

=========================================
