---- MODULE PossibleFail ----
EXTENDS Naturals
VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 3

\* State-level predicates.
AtOne       == x = 1
AllDone     == x = 2
Unreachable == x = 5     \* never true: reachable values of x are 0, 1, 2

\* Action-level predicates.
WrapAround == x = 2 /\ x' = 0
BigJump    == x' = x + 2 \* never true: Next only increments x by 1 mod 3

Spec == Init /\ [][Next]_x

\* Used by PossibleFailNoTransTest to exercise the edge case where there are
\* no transitions at all (only initial states).  Action-level predicates wired
\* through actionConstraints are never evaluated for such a spec, so the name
\* is never inserted into _Counts -- _CheckName must still report the failure.
NoNext       == FALSE
SpecOnlyInit == Init /\ [][NoNext]_x
====
