---- MODULE MC ----
EXTENDS MTest4, TLC

\* Specification formula
spec_124951411188626000 ==
(x=0) /\ (y=0) /\[][ FALSE ]_<<x, y>> 
----
\* INVARIANT definition
inv_124951411188627000 ==
x > y
----
====
\* Generated at Wed Aug 05 16:15:11 PDT 2009