---- MODULE MCa ----
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
const_14467710209401026000 == 
{e1, e2}
----

\* MV CONSTANT definitions Ids
const_14467710209501027000 == 
{i1, i2}
----

\* MV CONSTANT definitions DeQers
const_14467710209601028000 == 
{d1}
----

\* MV CONSTANT definitions Data
const_14467710209701029000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_14467710209801030000 == 
Permutations(const_14467710209401026000) \union Permutations(const_14467710209601028000)
----

\* CONSTANT definitions @modelParameterConstants:4InitData
const_14467710209901031000 == 
v1
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_14467710210501037000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_14467710210601038000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_14467710210701039000 ==
(\E e \in EnQers : enq[e] = v2) ~> (\E d \in DeQers : deq[d] = v2)
----
=============================================================================
\* Modification History
\* Created Thu Nov 05 16:50:21 PST 2015 by lamport
