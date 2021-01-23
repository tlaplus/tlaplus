---- MODULE Github362B ----

\* Auxiliary spec instantiated by Github362.tla.

EXTENDS TLC

CONSTANT C

VARIABLES x

\* This name also exists in Github362.tla with a different definition (it is a
\* variable rather than a user-defined operator).  The definition in Github362
\* should not conflict with this one.
overloadedName == x

overloadedConst == C

Init ==
    /\ Print(<<"Evaluating initial state in B; overloadedName is ", overloadedName>>, TRUE) \* x
    /\ overloadedName = "x" \* overloadedName -> variable x -> value "x"
    /\ x = "x"
    /\ Print(<<"Evaluating initial state in B; overloadedConst is ", overloadedConst>>, TRUE) \* 42
    /\ overloadedConst = 42 \* overloadedConst -> const C -> 42
    /\ C = 42

Next == UNCHANGED x
Spec == Init /\ [][Next]_x

==================
