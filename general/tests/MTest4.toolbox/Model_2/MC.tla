---- MODULE MC ----
EXTENDS MTest4, TLC

\* Specification formula
spec_124951373362820000 ==
(x=0) /\ (y=0) /\[][ FALSEE ]_<<x, y>> 
----
\* INVARIANT definition
inv_124951373364321000 ==
x \in {"a", "b"}
----
====
\* Generated at Wed Aug 05 16:08:53 PDT 2009