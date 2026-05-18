--------------------------- MODULE Github1389ViolatedC ---------------------------
EXTENDS Naturals, FiniteSets, TLCExt

VARIABLE x

RECURSIVE Reach(_)
Reach(n) == IF n = 0 THEN (x = 99) ELSE <>(Reach(n - 1))

Init == x = 0
Next == x' \in 0..99
Spec == Init /\ [][Next]_x /\ WF_x(Next)

PropViolated == Reach(3)

\* Postcondition asserting the shape of the counterexample.  WF_x(Next)
\* forces the lasso to actually move x rather than stutter, so TLC finds a
\* two-state cycle x = 0 -> x = v -> back to x = 0 for some v.  The
\* specific value v depends on state-space exploration order; v must be
\* in 1..98 because
\*   - v # 0:  WF_x(Next) requires a non-stuttering step, so x must change,
\*   - v # 99: the lasso violates <>(x = 99), so no state on it has x = 99.
PostCondition ==
    LET S == CounterExample.state
        A == CounterExample.action
        \* x-value of the non-initial state on the lasso (varies; in 1..98).
        s2v == LET t == CHOOSE t \in S : t[1] = 2 IN t[2].x
    IN
    /\ Cardinality(S) = 2
    /\ Cardinality(A) = 2
    /\ <<1, [x |-> 0]>> \in S
    /\ <<2, [x |-> s2v]>> \in S
    /\ s2v \in 1..98
    /\ \A a \in A : a[2].name = "Next"
    /\ \E a \in A : a[1] = <<1, [x |-> 0]>> /\ a[3] = <<2, [x |-> s2v]>>
    /\ \E a \in A : a[1] = <<2, [x |-> s2v]>> /\ a[3] = <<1, [x |-> 0]>>
==================================================================
