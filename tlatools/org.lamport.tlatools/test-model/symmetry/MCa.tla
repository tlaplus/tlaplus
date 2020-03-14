---- MODULE MCa ----
EXTENDS SymmetryLiveness3, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions S
const_143263724205431000 == 
{a, b}
----

\* SYMMETRY definition
symm_143263724206532000 == 
Permutations(const_143263724205431000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_143263724207533000 ==
Spec1
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_143263724208534000 ==
Prop1
----
=============================================================================
\* Modification History
\* Created Tue May 26 12:47:22 CEST 2015 by markus
