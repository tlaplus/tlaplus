--------------------------- MODULE AssignmentInitExpensive ---------------------------
EXTENDS Integers
VARIABLE s

\* expensiveOp takes ~10 seconds wallclock time on a modern day machine.
\* The point is, that doing 10k times will make the test time out.
expensiveOp == CHOOSE e \in SUBSET (1..18) : TRUE

\* This variant (with an unused parameter) causes TLC to reevaluate 
\* CHOOSE ... SUBSET 10k times.
\*expensiveOpParam(ignored) == CHOOSE e \in SUBSET (1..18) : TRUE

Init(var) == \E val \in 0..10000: var = expensiveOp

Spec == Init(s) /\ [][UNCHANGED s]_s

=============================================================================
