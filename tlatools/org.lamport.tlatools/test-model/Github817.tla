---------------------------- MODULE Github817 ---------------------------
VARIABLES x

Init == x = "init"
Next ==
    \/ x = "init" /\ x' = "in-progress"
    \/ x = "in-progress" /\ x' = "done"

AbstractX == IF x = "done" THEN "done" ELSE "in-progress"

Abstract == INSTANCE Abstract WITH
    x <- AbstractX

AbstractParam(n) == INSTANCE Abstract WITH
    x <- n

Spec ==
    /\ Init
    /\ [][Next]_x
    /\ WF_x(Next)


Refinement == Abstract!Spec
RefinementParam == AbstractParam(AbstractX)!Spec

op(b) == [][b]_x
PropParam == op(TRUE)               \* constant-level

\* Checking property PropParamRec causes a StackOverflow
RECURSIVE opRec(_)
opRec(b) == IF b THEN [][b]_x ELSE opRec(~b)
PropParamRec == opRec(TRUE)

PropParamF == op(FALSE)              \* constant-level

id(a) == a
TypeOK == x \in {"init", "in-progress", "done"}
PropParamIdState == id(TypeOK)       \* state-level

PropParamId == id(Refinement)        \* temporal-level

CheckBoth(safety, liveness) == safety /\ liveness
PropParamCheckBoth == CheckBoth(Refinement, op(TRUE))  \* both temporal-level

==========================================================================

----------------------------- MODULE Abstract ----------------------------
VARIABLES x
Super == INSTANCE Abstract2
Init == Super!Init
Next == Super!Next
Spec ==
    /\ Init
    /\ [][Next]_x
    /\ WF_x(Next)
==========================================================================

----------------------------- MODULE Abstract2 ---------------------------
VARIABLES x
Init == x = "in-progress"
Next == x' = "done"
Spec ==
    /\ Init
    /\ [][Next]_x
    /\ WF_x(Next)
==========================================================================

---------------------------- CONFIG Github817 ----------------------------
SPECIFICATION Spec
CHECK_DEADLOCK FALSE
PROPERTY Refinement PropParam
===========================================================================
