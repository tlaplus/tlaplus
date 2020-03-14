---- MODULE MC ----
EXTENDS VoteProof, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT definitions Acceptor
const_142667695488923000 == 
{a1, a2, a3}
----

\* CONSTANT definitions @modelParameterConstants:0Quorum
const_142667695489924000 == 
{{a1, a2}, {a1, a3}, {a2, a3}}
----

\* CONSTANT definitions @modelParameterConstants:1Value
const_142667695490925000 == 
{"v1","v2"}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_142667695492026000 ==
0..4
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_142667695493027000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_142667695494028000 ==
(TRUE ~> FALSE)
----
=============================================================================
\* Modification History
\* Created Wed Mar 18 12:09:14 CET 2015 by markus
