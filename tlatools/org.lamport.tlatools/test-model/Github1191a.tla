---- MODULE Github1191a ----

P == { "A", "B" }
C == P \X P

VARIABLES var

Init == 
    var = [c \in C |-> << >>]

Next ==
    \E src, dst \in P:
        var' = [var EXCEPT ![<<src, dst>>] = << [ type |-> "hello" ] >>]

Spec == Init /\ [][Next]_var

Termination == <>FALSE

====
---- CONFIG Github1191a ----
SPECIFICATION Spec
PROPERTY Termination
====