---- MODULE MC ----
EXTENDS DijkstraMutex, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3, p4
----

\* MV CONSTANT definitions Proc
const_1293897507996435000 == 
{p1, p2, p3, p4}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1293897508011436000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1293897508027437000 ==
MutualExclusion
----
=============================================================================
\* Modification History
\* Created Sat Jan 01 07:58:28 PST 2011 by lamport
