---- MODULE Github607 ----
EXTENDS Naturals

VARIABLE x

Init ==
    x = 0

Next ==
    /\ UNCHANGED x

Spec ==
    Init /\ [][Next]_x

Prop ==
    \* The consequent have to be state-level. A constant-level silly
    \* expression would be caught during tableau construction.
    \* In pratice, this would probably something like:
    \*    someSeq == <<...>>
    \*    x.idx \in DOMAIN someSeq ~> someSeq[x.idx]
    x \notin Nat ~> x = "abc"

====
---- CONFIG Github607 ----
SPECIFICATION
    Spec
PROPERTIES
    Prop
====