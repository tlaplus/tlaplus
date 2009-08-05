---- MODULE MC ----
EXTENDS MTest1, TLC

\* CONSTANT definitions
const_12495091923297000 == 
1
----

\* New definitions
foo == 2
----
\* Specification formula
spec_12495091923298000 ==
x=0 /\ [][x'=a]_x
----
====
\* Generated at Wed Aug 05 14:53:12 PDT 2009