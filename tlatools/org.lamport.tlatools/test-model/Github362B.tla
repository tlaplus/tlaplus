---- MODULE Github362B ----

\* Auxiliary spec instantiated by Github362.tla.

EXTENDS TLC

VARIABLES x

\* This name also exists in Github362.tla with a different definition (it is a
\* variable rather than a user-defined operator).  The definition in Github362
\* should not conflict with this one.
overloadedName == x

Init ==
    /\ Print(<<"Evaluating initial state in B; overloadedName is ", overloadedName>>, TRUE)
    /\ overloadedName = "x"
    /\ x = "x"

Next == UNCHANGED x
Spec == Init /\ [][Next]_x

==================
