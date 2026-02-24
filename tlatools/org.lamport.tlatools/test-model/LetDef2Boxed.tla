---- MODULE LetDef2Boxed ----
VARIABLE
    x
vars == x
x0 == x
Init == x = TRUE
Next == x' = ~x
Spec == Init /\ [][Next]_vars

x3(def_arg) == def_arg
Prop ==
    LET
        x1(x2(_)) == x2([][x']_x0)
    IN x1(x3)

-------

x2(def_arg) == def_arg
x1(def_arg(_)) == def_arg([][x']_x0)
Prop2 == x1(x2)

s1(sa(_)) == sa(Init /\ [][Next]_vars)

Spec3 ==
    LET
        id(a(_)) == a(Init /\ [][Next]_vars)
    IN id(x3)

Spec4 == s1(x3)

====
---- CONFIG LetDef2Boxed ----
SPECIFICATION Spec
PROPERTY Prop
====
