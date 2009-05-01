-------------------------- MODULE etest12 --------------------------------
EXTENDS Naturals, TLC, FiniteSets
\* Test of error reporting when computing Cardinality of a huge set.

ASSUME
     IF Cardinality ([0..2 -> 1..2000]) = Cardinality ([2..4 -> 1..2000]) 
       THEN Print("Test 22 OK", TRUE)
       ELSE Assert(FALSE, "Test 22 Failed")
==========================================================================