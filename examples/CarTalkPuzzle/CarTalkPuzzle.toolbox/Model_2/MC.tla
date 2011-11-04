---- MODULE MC ----
EXTENDS CarTalkPuzzle, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_131965207585635000 == 
15
----

\* CONSTANT definitions @modelParameterConstants:1P
const_131965207587136000 == 
4
----

\* Constant expression definition @modelExpressionEval
const_expr_131965207588737000 == 
AllSolutions
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_131965207588737000>>)
----

=============================================================================
\* Modification History
\* Created Wed Oct 26 11:01:15 PDT 2011 by lamport
