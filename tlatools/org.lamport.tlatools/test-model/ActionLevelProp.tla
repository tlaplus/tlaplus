---- MODULE ActionLevelProp ----
EXTENDS Naturals

VARIABLE x
vars == x

Init ==
    x = 0

Next ==
    /\ x < 5
    /\ x' = x + 1

Spec ==
    Init /\ [][Next]_vars

------

ActionLivePropA ==
    x' > x

ActionLivePropB ==
	Next

ActionLivePropC ==
    Next \/ UNCHANGED vars

ActionLivePropD ==
    [Next]_vars

ActionLivePropE ==
    <<Next>>_vars

=============================================================================
The following formulas are state level and, thus, out of scope.
    ENABLED Next
    ENABLED [Next]_vars
    ENABLED <<Next>>_vars
