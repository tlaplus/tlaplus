---- MODULE MC ----
EXTENDS MTest4, TLC

\* Specification formula
spec_124951442231630000 ==
(x=0) /\ (y=0) /\[][ FALSE ]_<<x, y>> 
----
\* PROPERTY definition
prop_124951442231631000 ==
<>(x = 1)
----
====
\* Generated at Wed Aug 05 16:20:22 PDT 2009