---- MODULE MC ----
EXTENDS MTest4, TLC

\* Specification formula
spec_124951396013024000 ==
(x=0) /\ (y \in [1..10 -> 1..5]) /\[][ FALSE ]_<<x, y>> 
----
====
\* Generated at Wed Aug 05 16:12:40 PDT 2009