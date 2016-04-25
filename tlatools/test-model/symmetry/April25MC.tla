---- MODULE April25MC ----
EXTENDS April25, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
m1, m2
----

\* MV CONSTANT definitions S
const_146115895642519000 == 
{m1, m2}
----

\* SYMMETRY definition
symm_146115895643520000 == 
Permutations(const_146115895642519000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_146115895644521000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_146115895645522000 ==
Live
----
=============================================================================
