---- MODULE MC ----
EXTENDS MTest5, TLC

\* Specification formula
spec_124951511992136000 ==
Init /\[][ (x'=x /\ y'=1-y) ]_<<x, y>> 
----
\* INVARIANT definition
inv_124951511992137000 ==
y=0
----
====
\* Generated at Wed Aug 05 16:31:59 PDT 2009