---- MODULE MC ----
EXTENDS MTest5, TLC

\* Specification formula
spec_124951725292645000 ==
Init /\[][ Next ]_<<x, y>> 
----
\* INVARIANT definition
inv_124951725294246000 ==
y < 1
----
====
\* Generated at Wed Aug 05 17:07:32 PDT 2009