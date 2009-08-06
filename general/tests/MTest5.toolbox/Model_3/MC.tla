---- MODULE MC ----
EXTENDS MTest5, TLC

\* Specification formula
spec_124951521011338000 ==
Init /\[][ (x'=x /\ y'=1-y) ]_<<x, y>> 
----
\* PROPERTY definition
prop_124951521011339000 ==
[][y'=y+1]_y
----
====
\* Generated at Wed Aug 05 16:33:30 PDT 2009