---- CONFIG EWD998_TTrace ----
CONSTANTS
N = 5 
_TETrace <- def_ov_16140408157492000

PROPERTY prop_16140408157533000

CHECK_DEADLOCK FALSE

INIT _SpecTEInit

NEXT _SpecTENext

ALIAS TTraceExpression
================

---- MODULE EWD998_TTrace ----
EXTENDS Toolbox, TLC, EWD998

ASSUME TRUE

\* TE declaration
TTraceExpression ==
    LET EWD998_TE == INSTANCE EWD998_TE
    IN EWD998_TE!TraceExpression

\* TraceDef definition
TTraceTraceDef == INSTANCE TTraceTraceDef
def_ov_16140408157492000 == TTraceTraceDef!def_ov_16140408157492000

\* PROPERTY definition
prop_16140408157533000 ==
~<>[](
    color = (
    (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white" @@ 4 :> "white")
    )    /\
    pending = (
    (0 :> 0 @@ 1 :> 0 @@ 2 :> 0 @@ 3 :> 0 @@ 4 :> 0)
    )    /\
    active = (
    (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE @@ 4 :> FALSE)
    )    /\
    counter = (
    (0 :> 0 @@ 1 :> 0 @@ 2 :> 0 @@ 3 :> 0 @@ 4 :> 0)
    )    /\
    token = (
    [pos |-> 4, q |-> 0, color |-> "white"]
    )
)
----

\* TRACE INIT definition traceExploreInit
_SpecTEInit ==
    /\ active = _TETrace[1].active
    /\ color = _TETrace[1].color
    /\ counter = _TETrace[1].counter
    /\ pending = _TETrace[1].pending
    /\ token = _TETrace[1].token

----

\* TRACE NEXT definition traceExploreNext
_SpecTENext ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ j = i + 1
        /\ active  = _TETrace[i].active
        /\ active' = _TETrace[j].active
        /\ color  = _TETrace[i].color
        /\ color' = _TETrace[j].color
        /\ counter  = _TETrace[i].counter
        /\ counter' = _TETrace[j].counter
        /\ pending  = _TETrace[i].pending
        /\ pending' = _TETrace[j].pending
        /\ token  = _TETrace[i].token
        /\ token' = _TETrace[j].token


=============================================================================

---- MODULE EWD998_TE ----
EXTENDS Toolbox, TLC, EWD998

TraceExpression == 
    [
        active |-> active
        ,color |-> color
        ,counter |-> counter
        ,pending |-> pending
        ,token |-> token
        \* Put additional trace expressions here; examples:
        \* ,x |-> ~y'
        \* ,e |-> ENABLED ActionName
    ]

=============================================================================

---- MODULE TTraceTraceDef ----
EXTENDS Toolbox, TLC, EWD998

def_ov_16140408157492000 == 
    <<
    ([color |-> (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white" @@ 4 :> "white"),pending |-> (0 :> 0 @@ 1 :> 0 @@ 2 :> 0 @@ 3 :> 0 @@ 4 :> 0),active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE @@ 4 :> FALSE),counter |-> (0 :> 0 @@ 1 :> 0 @@ 2 :> 0 @@ 3 :> 0 @@ 4 :> 0),token |-> [pos |-> 0, q |-> 0, color |-> "black"]]),
    ([color |-> (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white" @@ 4 :> "white"),pending |-> (0 :> 0 @@ 1 :> 0 @@ 2 :> 0 @@ 3 :> 0 @@ 4 :> 0),active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE @@ 4 :> FALSE),counter |-> (0 :> 0 @@ 1 :> 0 @@ 2 :> 0 @@ 3 :> 0 @@ 4 :> 0),token |-> [pos |-> 4, q |-> 0, color |-> "white"]])
    >>
----


=============================================================================
