--------------------------- MODULE Github1389StateGuard ---------------------------
\* Regression test for https://github.com/tlaplus/tlaplus/issues/1389
\* exercising the error-handling path when a RECURSIVE operator at
\* temporal level is applied to a state-level argument.

EXTENDS Naturals

VARIABLE x

RECURSIVE op(_)
op(n) == IF n = 0 THEN <>(x = 0) ELSE op(n - 1)

Init == x = 0
Next == x' \in 0..3
Spec == Init /\ [][Next]_x

\* op's parameter is bound to x (state-level); the guard `n = 0`
\* therefore references a state variable and never resolves during
\* tableau construction.
Prop == op(x)
==================================================================
