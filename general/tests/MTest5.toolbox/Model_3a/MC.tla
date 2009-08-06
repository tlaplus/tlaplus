---- MODULE MC ----
EXTENDS MTest5, TLC

\* Specification formula
spec_124951961975175000 ==
Init /\[][ (x'=x /\ y'=1-y) ]_<<x, y>> 
----
\* PROPERTY definition
prop_124951961975176000 ==
[]<><<y = 1 => y'="a">>_y
----
====
\* Generated at Wed Aug 05 17:46:59 PDT 2009