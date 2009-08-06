---- MODULE MC ----
EXTENDS MTest5, TLC

\* Specification formula
spec_124951731975747000 ==
Init /\[][ Next ]_<<x, y>> 
----
\* PROPERTY definition
prop_124951731975748000 ==
[][y'>y]_y
----
====
\* Generated at Wed Aug 05 17:08:39 PDT 2009