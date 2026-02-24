--------------------------- MODULE LetDef1Boxed ----------------------------
VARIABLE
    x
vars == x
x0 == x
Init == x = TRUE
Next == x' = ~x
Spec == Init /\ [][Next]_vars

Prop ==
    LET
        x1(x2) == x2
    IN x1([][x']_x0)

-----

x1(def_arg) == def_arg

Prop2 == x1([][x']_x0)

Spec3 ==
    LET
        id(a) == a
    IN id(Init /\ [][Next]_vars)

Spec4 == x1(Init /\ [][Next]_vars)
===========================================================================
---- CONFIG LetDef1Boxed ----
SPECIFICATION Spec
PROPERTY Prop
======