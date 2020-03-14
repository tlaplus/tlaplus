---- MODULE MC ----
EXTENDS NQSpecImpliesQSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
e1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
id1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1
----

\* MV CONSTANT definitions EnQers
const_14476073153412000 == 
{e1}
----

\* MV CONSTANT definitions Ids
const_14476073153513000 == 
{id1}
----

\* MV CONSTANT definitions DeQers
const_14476073153614000 == 
{d1}
----

\* MV CONSTANT definitions Data
const_14476073153715000 == 
{v1}
----

\* CONSTANT definitions @modelParameterConstants:4InitData
const_14476073153816000 == 
v1
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_144760731543311000 ==
SpecI
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_144760731544312000 ==
TypeOKI
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_144760731545313000 ==
I!Spec
----
=============================================================================
\* Modification History
\* Created Sun Nov 15 18:08:35 CET 2015 by markus
