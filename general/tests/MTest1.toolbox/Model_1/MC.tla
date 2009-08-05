---- MODULE MC ----
EXTENDS MTest1, TLC

\* Specification formula
spec_12495080839932000 ==
x = /\[][ x' = x+ ]_<<x>> 
----
====
\* Generated at Wed Aug 05 14:34:43 PDT 2009