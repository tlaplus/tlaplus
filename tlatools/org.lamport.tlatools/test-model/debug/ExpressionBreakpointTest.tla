---- MODULE ExpressionBreakpointTest ----
EXTENDS Naturals
VARIABLE i
CONSTANT j
ASSUME j \in Nat
op(k) ==
  \A l \in 0 .. (j - k) :
    i \in Nat
Inv == op(5)
Init == i = 0
Next == IF i < j THEN i' = i + 1 ELSE UNCHANGED i
====
---- CONFIG ExpressionBreakpointTest ----
CONSTANT j = 10
INVARIANTS Inv
INIT Init
NEXT Next
====

