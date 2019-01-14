---------------------------- MODULE D ----------------------------
EXTENDS Naturals
VARIABLE x

Init == x = 0

(* No endless recursion in Coverage/Cost with RECURSIVE. *)
RECURSIVE fact(_)
fact(n) == IF n = 1 THEN 1 ELSE n * fact(n - 1)

A == x' = fact(3)

B == x' = fact(9)

Next == A \/ B

Spec == Init /\ [][Next]_<<x>>
=============================================================================
