---- MODULE MC ----
EXTENDS MTest5, TLC

\* New definitions
foobar == 
   (x'=x /\ y'=1-y) \/ (y=1 /\ y' = y\div 0)
----
\* Specification formula
spec_124951715017144000 ==
Init /\[][ foobar ]_<<x, y>> 
----
====
\* Generated at Wed Aug 05 17:05:50 PDT 2009