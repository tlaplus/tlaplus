---- MODULE MC ----
EXTENDS SPA_Attack, TLC

\* CONSTANT definitions @modelParameterConstants:0ClientCfg
const_1673873984308273000 == 
[LoginID |->1,Key |-> 44,SrcIp |->11]
----

\* CONSTANT definitions @modelParameterConstants:1SDPSvrCfg
const_1673873984308274000 == 
[IP |-> 12,Port |-> 8000]
----

\* CONSTANT definitions @modelParameterConstants:2SvrCfg
const_1673873984308275000 == 
[IP |-> 22,Port |-> 80]
----

\* CONSTANT definitions @modelParameterConstants:3MATCH_ANY
const_1673873984308276000 == 
65536
----

\* CONSTANT definitions @modelParameterConstants:4USER_BASEPORT
const_1673873984308277000 == 
1024
----

\* CONSTANT definitions @modelParameterConstants:5ATTACKER_BASEPORT
const_1673873984308278000 == 
2024
----

\* CONSTANT definitions @modelParameterConstants:6AttackerCfg
const_1673873984308279000 == 
[SrcIp |-> 11]
----

\* CONSTANT definitions @modelParameterConstants:7NAT_FLAG
const_1673873984308280000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:8UNKNOWN_AUTH_ID
const_1673873984308281000 == 
65535
----

=============================================================================
\* Modification History
\* Created Mon Jan 16 20:59:44 CST 2023 by 10227694
