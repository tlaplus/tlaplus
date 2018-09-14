------------------------------ MODULE BasicMultiTrace ------------------------------
EXTENDS Integers

\*
\* This spec attempts to define the simplest state machine that 
\* has more than one behavior. Originally added to verify correctness of simulation
\* mode in both single and multi-threaded mode.
\*

VARIABLE branch, depth

MaxDepth == 5
Width == 10

Init == 
    /\ branch = 0
    /\ depth = 0

Next == 
    \* Pick a branch
    \/ /\ branch = 0
       /\ branch' \in 1..Width /\ UNCHANGED depth
    \* Traverse down that branch.
    \/ /\ branch > 0 
       /\ depth < MaxDepth
       /\ depth' = depth + 1 /\ UNCHANGED branch

Spec == Init /\ [][Next]_<<branch, depth>>

UnderspecifiedNext == branch' = 0
UnderspecifiedInit == branch = 0

UnderspecifiedInitSpec == UnderspecifiedInit /\ [][Next]_<<branch, depth>>
UnderspecifiedNextSpec == Init /\ [][UnderspecifiedNext]_<<branch, depth>>

\* A valid invariant that should be violated by the initial state.
InvInitState == ~(branch = 0)

\* A valid invariant that should be violated by the spec.
Inv == ~(branch = 1)

\* A nonsensical invariant that will cause a runtime evaluation error on the initial state.
InvBadEvalInitState == (0 = "a")

\* A nonsensical invariant that will cause a runtime evaluation error on a non-initial state.
InvBadEvalNonInitState == IF branch = 0 THEN TRUE ELSE (0 = "a")

TemporalProp == <>(branch = 15)

=============================================================================