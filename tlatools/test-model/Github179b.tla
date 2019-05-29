---- MODULE Github179b ----
EXTENDS TLC, Naturals

VARIABLE v

Max(s) == { x \in s : \A y \in s : x >= y}

sillyExpr == 
{s \in SUBSET {1,2,3,4} : \A x \in s : IF x = Max(s) THEN TRUE ELSE (x+1) \in s}
----

Init ==
Print(sillyExpr, FALSE)/\v = 0
----
Next ==
FALSE/\ v'= v
----
=============================================================================
