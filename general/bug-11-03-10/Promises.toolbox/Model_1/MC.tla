---- MODULE MC ----
EXTENDS Promises, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
id1, id2, id3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
exc1, exc2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Id
const_1299801378174356000 == 
{id1, id2, id3}
----

\* MV CONSTANT definitions Exception
const_1299801378184357000 == 
{exc1, exc2}
----

\* MV CONSTANT definitions Value
const_1299801378194358000 == 
{v1, v2}
----

\* CONSTANT definitions @modelParameterConstants:3Type
const_1299801378204359000 == 
{EventualType}
----

\* CONSTANT definitions @modelParameterConstants:4Field
const_1299801378214360000 == 
{"type", "f1", "f2"}
----

\* New definitions @modelParameterNewDefinitions
TestHeap ==
(id1 :> [ f1 |-> id2, 
          f2 |-> <<v1, id3>>])
  @@
(id2 :> << >>)
  @@
(id3 :> << >>)

TestObj ==
[type |-> EventualType,
 f1 |-> id1]
----
\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1299801378224361000 ==
0..5
----
\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1299801378234362000(S) ==
UNION { [1..n -> S] : n \in 0..2 }
----
\* Constant expression definition @modelExpressionEval
const_expr_1299801378244363000 == 
<<TestObj \in Object,
 ReachableFrom(TestObj, TestHeap)
>>
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1299801378244363000>>)
----

=============================================================================
\* Modification History
\* Created Thu Mar 10 15:56:18 PST 2011 by lamport
