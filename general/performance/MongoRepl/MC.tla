---- MODULE MC ----
EXTENDS RaftMongo, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s1, s2, s3
----

\* MV CONSTANT definitions Value
const_1518107340940126000 == 
{v1}
----

\* MV CONSTANT definitions Server
const_1518107340940127000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_1518107340940128000 == 
Permutations(const_1518107340940127000)
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1518107340940129000 ==
/\ \forall i \in Server: globalCurrentTerm <= 6
/\ \forall i \in Server: Len(log[i]) <= 15
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1518107340940130000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1518107340940131000 ==
NeverRollbackCommitted
----
=============================================================================
