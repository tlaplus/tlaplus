---- MODULE MC ----
EXTENDS MTest4, TLC

\* Specification formula
spec_124951199249519000 ==
x = {1, "2"} /\ y = 1 /\[][ FALSE ]_<<x, y>> 
----
====
\* Generated at Wed Aug 05 15:39:52 PDT 2009