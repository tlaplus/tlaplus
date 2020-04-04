---- MODULE Github179a ----
EXTENDS TLC, Naturals

VARIABLE v

Max(s) == { x \in s : \A y \in s : x >= y}

(* Attempted to check equality of integer 1 with non-integer: {1} *)
sillyExpr == 
   {s \in SUBSET {1,2,3} : 
               \A x \in s : IF x = Max(s) 
                            THEN TRUE
                            ELSE (x+1) \in s}
----

ASSUME PrintT(<<"$!@$!@$!@$!@$!", sillyExpr>>)
----

Init ==
FALSE/\v = 0
----
Next ==
FALSE/\ v'= v
----
=============================================================================
