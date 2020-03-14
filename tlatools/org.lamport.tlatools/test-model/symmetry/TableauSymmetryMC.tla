---- MODULE TableauSymmetryMC ----
EXTENDS TableauSymmetry, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Val
const_144481269486926000 == 
{a, b}
----

\* SYMMETRY definition
symm_144481269487927000 == 
Permutations(const_144481269486926000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_144481269488928000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_144481269489929000 ==
Liveness
----
=============================================================================
