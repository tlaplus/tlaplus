---- MODULE MC ----
EXTENDS MTest4, TLC

\* Specification formula
spec_124951418921828000 ==
(x=0) /\ (y=0) /\[][ FALSE ]_<<x, y>> 
----
\* PROPERTY definition
prop_124951418921829000 ==
x = 1
----
====
\* Generated at Wed Aug 05 16:16:29 PDT 2009