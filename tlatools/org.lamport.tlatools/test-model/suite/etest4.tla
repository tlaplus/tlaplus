--------------- MODULE etest4  -------------

(* Evaluates m[v] for model-value m. *)

EXTENDS TLC, Naturals, Sequences, FiniteSets

VARIABLE x
CONSTANT A



Req == [  mask |-> A  ]
Init == /\ x = 1
        /\ Print("Should report error for applying model value to arg", TRUE)
        /\ Req.mask[1] = 1
        /\ Print("Should never get this far", TRUE)

Next == UNCHANGED x

Inv ==  TRUE

=========================================
