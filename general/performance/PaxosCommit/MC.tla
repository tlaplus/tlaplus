---- MODULE MC ----
EXTENDS PaxosCommit, TLC, stats

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
rm1, rm2
----

\* MV CONSTANT definitions Acceptor
const_145717642420826000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions RM
const_145717642421827000 == 
{rm1, rm2}
----

\* SYMMETRY definition
symm_145717642422828000 == 
Permutations(const_145717642420826000) \union Permutations(const_145717642421827000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballot
const_145717642423829000 == 
{0, 1, 2}
----

\* CONSTANT definitions @modelParameterConstants:2Majority
const_145717642424830000 == 
{{a1, a2}, {a1, a3}, {a2, a3}}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_145717642425831000 ==
PCSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_145717642426932000 ==
PCTypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_145717642427933000 ==
TC!TCSpec
----
=============================================================================
\* Modification History
\* Created Sat Mar 05 12:13:44 CET 2016 by markus
