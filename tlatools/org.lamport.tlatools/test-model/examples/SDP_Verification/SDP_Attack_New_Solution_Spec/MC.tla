---- MODULE MC ----
EXTENDS SPA_Attack_New, TLC

\* CONSTANT definitions @modelParameterConstants:0SDPSvrCfg
const_1645172937699121000 == 
[IP |-> 12,Port |-> 8000]
----

\* CONSTANT definitions @modelParameterConstants:1NAT_FLAG
const_1645172937699122000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2USER_BASEPORT
const_1645172937699123000 == 
1024
----

\* CONSTANT definitions @modelParameterConstants:3MATCH_ANY
const_1645172937699124000 == 
65536
----

\* CONSTANT definitions @modelParameterConstants:4UNKNOWN_AUTH_ID
const_1645172937699125000 == 
65535
----

\* CONSTANT definitions @modelParameterConstants:5AttackerCfg
const_1645172937699126000 == 
[SrcIp |-> 11]
----

\* CONSTANT definitions @modelParameterConstants:6ClientCfg
const_1645172937699127000 == 
[LoginID |->1,Key |-> 44,SrcIp |->11]
----

\* CONSTANT definitions @modelParameterConstants:7ATTACKER_BASEPORT
const_1645172937699128000 == 
2024
----

\* CONSTANT definitions @modelParameterConstants:8SvrCfg
const_1645172937699129000 == 
[IP |-> 22,Port |-> 80]
----

=============================================================================
\* Modification History
\* Created Fri Feb 18 16:28:57 CST 2022 by 10227694
