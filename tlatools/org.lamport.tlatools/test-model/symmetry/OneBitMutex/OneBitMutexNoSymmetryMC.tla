---- MODULE OneBitMutexNoSymmetryMC ----
EXTENDS OneBitMutex, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B
----

\* MV CONSTANT definitions Procs
const_144491423291817000 == 
{A, B}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_144491423292818000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_144491423293819000 ==
StarvationFreedom
----
=============================================================================
