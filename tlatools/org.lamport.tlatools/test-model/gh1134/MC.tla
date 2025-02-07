---- MODULE MC ----
EXTENDS MultiUser

\* CONSTANT definitions @modelParameterConstants:0UserIDs
const_17385913267612000 == 
1..2
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_SingleUser2 ==
    SingleUser2!Spec

prop_SingleUser3 ==
    SingleUser3!Spec

prop_SingleUserP2 ==
    SingleUserP(2)!Spec

prop_SingleUserP3 ==
    SingleUserP(3)!Spec

prop_SingleUserAll2 ==
    \A n \in {2} : SingleUserP(n)!Spec

prop_SingleUserAll3 ==
    \A n \in {3} : SingleUserP(n)!Spec
=============================================================================