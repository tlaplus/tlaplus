---- MODULE MC ----
EXTENDS PaxosMadeSimple, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Acceptor
const_144139943710210000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions Value
const_144139943711311000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_144139943712312000 == 
Permutations(const_144139943710210000) \union Permutations(const_144139943711311000)
----

\* CONSTANT definitions @modelParameterConstants:2Quorum
const_144139943713313000 == 
{Q \in SUBSET Acceptor : Cardinality(Q) > Cardinality(Acceptor)\div 2}
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_144139943715315000 ==
0..4
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_144139943716316000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_144139943717317000 ==
Correctness
----
=============================================================================
\* Modification History
\* Created Fri Sep 04 16:43:57 EDT 2015 by nano
