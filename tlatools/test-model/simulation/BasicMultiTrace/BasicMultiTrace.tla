------------------------------ MODULE BasicMultiTrace ------------------------------
EXTENDS Integers

\*
\* This spec attempts to define a simple state machine that has multiple behaviors. 
\* Originally added to verify correctness of simulation mode in both single and multi-threaded mode.
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
Inv == ~(depth = 2)

\* A nonsensical invariant that will cause a runtime evaluation error on the initial state.
InvBadEvalInitState == (0 = "a")

\* A nonsensical invariant that will cause a runtime evaluation error on a non-initial state.
InvBadEvalNonInitState == IF branch = 0 THEN TRUE ELSE (0 = "a")

\* A valid action property that should be violated by the spec.
ActionProp == [][branch' > branch]_<<branch, depth>>

\* A nonsensical action property that will cause a runtime evaluation error.
ActionPropBadEval == [][IF branch = 0 THEN TRUE ELSE 0 = "a"]_<<branch, depth>>

\* A simple state and action constraint, and an invariant that should hold true 
\* given either constraint.
StateConstraint == depth < 4
ActionConstraint == ~(depth' = 4 /\ depth = 3)
InvConstraint   == depth <= 4

\* A liveness property that should be violated.
LivenessProp == <>(branch = -1)


=============================================================================