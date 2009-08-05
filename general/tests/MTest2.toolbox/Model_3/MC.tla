---- MODULE MC ----
EXTENDS MTest2, TLC

\* Specification formula
spec_12495109754386000 ==
(x=0) /\ [][x'=x]_x
----
\* PROPERTY definition
prop_12495109754387000 ==
[]<>[][x'=0]_x
----
====
\* Generated at Wed Aug 05 15:22:55 PDT 2009