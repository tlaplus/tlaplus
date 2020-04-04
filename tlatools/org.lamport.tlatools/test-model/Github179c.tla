---- MODULE Github179c ----
EXTENDS TLC, Naturals

VARIABLE v

Max(s) == { x \in s : \A y \in s : x >= y}

sillyExpr == 
{s \in SUBSET {1,2,3,4} : 
          \A x \in s : IF x = Max(s) 
                       THEN TRUE 
                       ELSE (x+1) \in s}

Init == v = 0

Next == PrintT(sillyExpr) = FALSE /\ v'= v
=====
