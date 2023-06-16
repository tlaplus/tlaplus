---------------------------- MODULE Github819 ---------------------------
EXTENDS Naturals
  
VARIABLES i

Init == i = 0
Next == i < 5 /\ i' = i + 1

Spec == Init /\ [][Next]_i

--------------------------
(*** Liveness ***)

TestFailing ==
  \A x \in {} :
    []<>TRUE

TestSucceeding ==
  \A x \in {42} :
    []<>TRUE

Live ==
  \* This condition causes liveness checking to fail with the error:
  \*  "Temporal formulas containing actions must be of forms <>[]A or []<>A."
  \* 
  \* If you comment this condition out, you'll see that liveness checking
  \* succeeds.
  /\ TestFailing

  \*/\ TestSucceeding
==========================================================================
---------------------------- CONFIG Github819 ----------------------------
SPECIFICATION Spec

PROPERTY Live
===========================================================================
