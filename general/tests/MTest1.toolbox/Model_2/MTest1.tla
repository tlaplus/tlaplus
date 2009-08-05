------------------------------- MODULE MTest1 ------------------------------- 

\* Generate parsing error in MC file
\*  Put the following in the Model:
\*   Spec:  (x=0) /\ [][x'=0]_

CONSTANT a
VARIABLE x

foo == 1
=============================================================================
