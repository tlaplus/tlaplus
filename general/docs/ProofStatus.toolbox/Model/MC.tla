---- MODULE MC ----
EXTENDS ProofStatus, TLC

\* CONSTANT definitions @modelParameterConstants:0ProofStatesSpec
const_127808783131070000 == 
<< << "s1", "s2" >>, 
   << "s3" >>, 
   <<"s1", "s2", "s4" >>,
   <<"s3", "s4">>
>>
----

\* Constant expression definition @modelExpressionEval
const_expr_127808783132671000 == 
<< Sum( <<2, 3, 4>> ),
   Product (<< 4, 3, 2 >>),
   IsNumbering,
   StateEnumerationAssumption >>
 
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_127808783132671000>>)
----

=============================================================================
\* Modification History
\* Created Fri Jul 02 09:23:51 PDT 2010 by lamport
