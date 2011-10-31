---- MODULE MC ----
EXTENDS CarTalkPuzzle, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_131986752160123000 == 
40
----

\* CONSTANT definitions @modelParameterConstants:1P
const_131986752161624000 == 
4
----

\* Constant expression definition @modelExpressionEval
const_expr_131986752163225000 == 
\* ExpandSolutions
\* CHOOSE B \in Break : IsSolution(B)
<<3^5 - 1, 40 + 3^4>>
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_131986752163225000>>)
----

=============================================================================
\* Modification History
\* Created Fri Oct 28 22:52:01 PDT 2011 by lamport
