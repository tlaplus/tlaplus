---- MODULE MC ----
EXTENDS MTest4, TLC

\* Specification formula
spec_124951403175825000 ==
(x=0) /\[][ FALSE ]_<<x, y>> 
----
====
\* Generated at Wed Aug 05 16:13:51 PDT 2009