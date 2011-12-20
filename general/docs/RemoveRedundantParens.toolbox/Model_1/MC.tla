---- MODULE MC ----
EXTENDS RemoveRedundantParens, TLC

\* CONSTANT definitions @modelParameterConstants:0TokId
const_132434501149312000 == 
{1,2}
----

\* Constant expression definition @modelExpressionEval
const_expr_132434501152413000 == 
ExprOfMaxLen(3)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_132434501152413000>>)
----

=============================================================================
\* Modification History
\* Created Mon Dec 19 17:36:51 PST 2011 by lamport
