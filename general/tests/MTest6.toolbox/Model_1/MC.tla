---- MODULE MC ----
EXTENDS MTest6, TLC

\* Specification formula
spec_124951765474151000 ==
Init /\[][ Next ]_<<x, y>> 
----
\* PROPERTY definition
prop_124951765475752000 ==
<>(x=3)
----
====
\* Generated at Wed Aug 05 17:14:14 PDT 2009