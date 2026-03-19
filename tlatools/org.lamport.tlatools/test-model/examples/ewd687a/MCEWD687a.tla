---- MODULE MCEWD687a ----
EXTENDS EWD687a, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
L, P1, P2, P3
----

\* MV CONSTANT definitions Procs
const_1633116534008310000 == 
{L, P1, P2, P3}
----

\* CONSTANT definitions @modelParameterConstants:1Edges
const_1633116534008311000 == 
{<<L, P1>>, <<P1, P2>>, <<P1, P2>>, <<P2, P1>>, <<P2,P3>>}
----

\* CONSTANT definitions @modelParameterConstants:2Leader
const_1633116534008312000 == 
L
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1633116534008313000 ==
\A e \in Edges : msgs[e] < 3 /\ acks[e] < 3 /\ sentUnacked[e] < 2 /\ rcvdUnacked[e] < 2

=============================================================================
\* Modification History
\* Created Fri Oct 01 12:28:54 PDT 2021 by lamport
