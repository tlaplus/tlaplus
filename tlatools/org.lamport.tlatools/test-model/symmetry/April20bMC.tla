---- MODULE April20bMC ----
EXTENDS April20b, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
m1, m2
----

\* MV CONSTANT definitions S
const_146115906599338000 == 
{m1, m2}
----

\* SYMMETRY definition
symm_146115906600339000 == 
Permutations(const_146115906599338000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_146115906601340000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_146115906602341000 ==
Live
----
=============================================================================
