---- MODULE MC ----
EXTENDS NQSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
e1, e2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
i1, i2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions EnQers
const_14467714432321108000 == 
{e1, e2}
----

\* MV CONSTANT definitions Ids
const_14467714432421109000 == 
{i1, i2}
----

\* MV CONSTANT definitions DeQers
const_14467714432521110000 == 
{d1}
----

\* MV CONSTANT definitions Data
const_14467714432621111000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_14467714432721112000 == 
Permutations(const_14467714432321108000) \union Permutations(const_14467714432521110000)
----

\* CONSTANT definitions @modelParameterConstants:4InitData
const_14467714432821113000 == 
v1
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_14467714433421119000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_14467714433521120000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_14467714433621121000 ==
(\E e \in elts : e.data = v2) ~> (\E d \in DeQers : deq[d] = v2)
----
=============================================================================
\* Modification History
\* Created Thu Nov 05 16:57:23 PST 2015 by lamport
