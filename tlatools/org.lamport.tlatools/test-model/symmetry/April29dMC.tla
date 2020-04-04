---- MODULE April29dMC ----
EXTENDS April29, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions S
const_146183938495726000 == 
{a, b}
----

\* SYMMETRY definition
symm_146183938496727000 == 
Permutations(const_146183938495726000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_146183938497728000 ==
SpecD
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_146183938498729000 ==
[]<>(x=a) /\ []<>(x=b)
----
=============================================================================
