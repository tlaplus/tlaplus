---- MODULE MC ----
EXTENDS MTest4, TLC

\* Specification formula
spec_124951858537659000 ==
(x=0) /\ (y=0) /\[][ FALSE ]_<<x, y>> 
----
\* PROPERTY definition
prop_124951858539260000 ==
(x="a")
----
====
\* Generated at Wed Aug 05 17:29:45 PDT 2009