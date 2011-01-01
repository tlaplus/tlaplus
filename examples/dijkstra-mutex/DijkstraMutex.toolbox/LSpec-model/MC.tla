---- MODULE MC ----
EXTENDS DijkstraMutex, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions Proc
const_1293897152927428000 == 
{p1, p2, p3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1293897152943429000 ==
LSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1293897152959430000 ==
MutualExclusion
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1293897152974431000 ==
DeadlockFreedom
----
=============================================================================
\* Modification History
\* Created Sat Jan 01 07:52:32 PST 2011 by lamport
