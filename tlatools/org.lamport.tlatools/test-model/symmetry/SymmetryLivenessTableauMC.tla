---- MODULE SymmetryLivenessTableauMC ----
EXTENDS SymmetryLivenessTableau, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c, d
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
e, f
----

\* MV CONSTANT definitions Val
const_144172195407986000 == 
{a, b}
----

\* MV CONSTANT definitions Proc
const_144172195408987000 == 
{c, d}
----

\* MV CONSTANT definitions Adr
const_144172195409988000 == 
{e, f}
----

\* SYMMETRY definition
symm_144172195410989000 == 
Permutations(const_144172195407986000) \union Permutations(const_144172195408987000) \union Permutations(const_144172195409988000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_144172195413091000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_144172195414092000 ==
Liveness
----
=============================================================================
