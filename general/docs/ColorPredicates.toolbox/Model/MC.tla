---- MODULE MC ----
EXTENDS ColorPredicates, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3, a4
----

\* MV CONSTANT definitions State
const_127799915384350000 == 
{a1, a2, a3, a4}
----

\* CONSTANT definitions @modelParameterConstants:1StateEnumeration
const_127799915385351000 == 
 [i \in VectorDomain |->
   CASE i = 0 -> a1
     [] i = 1 -> a2
     [] i = 2 -> a3
     [] i = 3 -> a4 ]
----

\* Constant expression definition @modelExpressionEval
const_expr_127799915386352000 == 
<<UnionTheorem, VectorComputation>>
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_127799915386352000>>)
----

=============================================================================
\* Modification History
\* Created Thu Jul 01 08:45:53 PDT 2010 by lamport
