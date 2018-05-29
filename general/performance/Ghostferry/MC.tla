---- MODULE MC ----
EXTENDS ghostferry, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r0, r1, r2
----

\* MV CONSTANT definitions Records
const_152748923762611000 == 
{r0, r1, r2}
----

\* CONSTANT definitions @modelParameterConstants:2MaxPrimaryKey
const_152748923762612000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:4InitialTable
const_152748923762613000 == 
<<r0, r1, r2, NoRecordHere>>
----

\* CONSTANT definitions @modelParameterConstants:8MaxBinlogSize
const_152748923762614000 == 
4
----

\* ACTION_CONSTRAINT definition @modelParameterActionConstraint:0
action_constr_152748923762616000 ==
BinlogSizeActionConstraint
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_152748923762617000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_152748923762618000 ==
SourceTargetEquality
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_152748923762619000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Mon May 28 08:33:57 CEST 2018 by markus
