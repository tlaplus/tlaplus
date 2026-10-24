---- MODULE DiffTraceTypeChange ----
EXTENDS Naturals
VARIABLES x, y

\* x changes from a string to an integer in the first step. TLC cannot compare
\* the two values.
Init == x = "none" /\ y = 0

Next == y < 3 /\ x' = 0 /\ y' = y + 1

\* Violated by the fourth state.
Inv == y < 3

\* Fair behaviors take all three steps and then stutter with y = 3, which
\* violates Liveness. The fairness is on y alone, because WF_<<x, y>> would
\* compare x' with x.
Spec == Init /\ [][Next]_<<x, y>> /\ WF_y(Next)

Liveness == []<>(y = 0)
====
