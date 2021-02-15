
  I didn't want to update the line numbers in the JUnit test.

------------------------------- MODULE Debug02 -------------------------------
VARIABLE x
Init == x = TRUE
Next == x' =~x
Spec == Init /\ [][Next]_x
CONSTANT C
val == 42
==================================================================================
------------------------------- CONFIG Debug02 -------------------------------
SPECIFICATION Spec
CONSTANT C <- val
==================================================================================
