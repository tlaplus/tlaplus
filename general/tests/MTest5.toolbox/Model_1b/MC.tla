---- MODULE MC ----
EXTENDS MTest5, TLC

\* Specification formula
spec_124951748129649000 ==
Init /\[][ Next ]_<<x, y>> 
----
\* PROPERTY definition
prop_124951748129650000 ==
WF_<<x,y>>(y=1 /\ x'="a")
----
====
\* Generated at Wed Aug 05 17:11:21 PDT 2009