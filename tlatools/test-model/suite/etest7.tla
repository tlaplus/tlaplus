--------------- MODULE etest7  -------------

(* Test replacement of constant with nonconstant operator. *)

EXTENDS TLC, Naturals, Sequences

CONSTANT C

VARIABLE x

Foo == x

Next == x' = C

Init == /\ Print("TLC should complain about replacing the constant C", TRUE)
        /\ Print("by the nonconstant Foo", TRUE)
        /\ x = 2

Inv ==  x = 2

=========================================
