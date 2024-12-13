---- MODULE ExpressionBreakpointTest ----
EXTENDS Naturals
VARIABLE i
CONSTANT j
op(k) ==
  \A l \in 0 .. k :
    LET m == i IN
      TRUE
Inv == op(i)
Init == i = 0
Next == IF i < j THEN i' = i + 1 ELSE UNCHANGED i
====
---- CONFIG ExpressionBreakpointTest ----
CONSTANT j = 10
INVARIANT Inv
INIT Init
NEXT Next
====

