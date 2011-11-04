---- MODULE MC ----
EXTENDS CarTalkPuzzle, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_131986786702435000 == 
121
----

\* CONSTANT definitions @modelParameterConstants:1P
const_131986786704036000 == 
5
----

\* Constant expression definition @modelExpressionEval
const_expr_131986786705637000 == 
AllSolutions
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_131986786705637000>>)
----

=============================================================================
\* Modification History
\* Created Fri Oct 28 22:57:47 PDT 2011 by lamport
