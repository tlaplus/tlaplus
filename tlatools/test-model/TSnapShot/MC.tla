---- MODULE MC ----
EXTENDS TSnapShot, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1
----

\* MV CONSTANT definitions Writer
const_1446808092434108000 == 
{w1}
----

\* MV CONSTANT definitions Reader
const_1446808092444109000 == 
{r1}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1446808092454110000 ==
0..2
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1446808092464111000 ==
LET maxNat == CHOOSE n \in Nat : \A m \in Nat : n >= m IN
\A w \in Writer : iwriter[w] < maxNat
----
\* Constant expression definition @modelExpressionEval
const_expr_1446808092474112000 == 
(w1 :> (w1 :> (w1 :> 0)) @@ r1 :> (w1 :> (w1 :> 0))) \in [Process -> [Writer -> Memory]]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1446808092474112000>>)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1446808092484113000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1446808092494114000 ==
TypeOK2
----
=============================================================================
\* Modification History
\* Created Fri Nov 06 12:08:12 CET 2015 by markus
