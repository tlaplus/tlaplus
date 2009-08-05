---- MODULE MC ----
EXTENDS MTest4, TLC

\* Specification formula
spec_124951382325222000 ==
(x=0) /\ (y=0) /\[][ FALSE ]_<<x, y>> 
----
\* PROPERTY definition
prop_124951382325223000 ==
<>(x="a")
----
====
\* Generated at Wed Aug 05 16:10:23 PDT 2009