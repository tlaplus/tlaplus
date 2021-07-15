--------------- MODULE test220  -------------

(* Testing deadlock and number of states found. *)

EXTENDS TLC, Naturals, Sequences, FiniteSets

ASSUME TLCGet("config").deadlock = FALSE

VARIABLE x, y, z

Init == /\ Print("This test should not deadlock when configured with CHECK_DEADLOCK=FALSE", TRUE)
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
