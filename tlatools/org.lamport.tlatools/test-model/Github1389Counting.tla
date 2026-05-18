--------------------------- MODULE Github1389Counting ---------------------------
\* Regression test for https://github.com/tlaplus/tlaplus/issues/1389
\* exercising the "counting safety property" use case -- the primary
\* motivation for permitting RECURSIVE operators at temporal level.
\*
\* Bound the number of times an event may occur.  The canonical example
\* here is "x is TRUE in at most n disjoint intervals", equivalently 
\* "x becomes TRUE at most n times":
\*
\*   AtMost(0) == []~x                              \* never TRUE
\*   AtMost(1) == [](x => [](~x => []~x))           \* TRUE in at most 1 interval
\*   AtMost(2) == [](x => [](~x => [](x => [](~x => []~x))))
\*   ...

EXTENDS Naturals, FiniteSets, TLCExt

VARIABLE x

RECURSIVE AtMost(_)
AtMost(n) == IF n = 0 THEN []~x
                      ELSE [](x => [](~x => AtMost(n - 1)))

Init == x = FALSE
Next == x' \in BOOLEAN
Spec == Init /\ [][Next]_x

CountAtMostFour == AtMost(4)

------------------------------------------------------------------

PostCondition ==
    LET S == CounterExample.state
        A == CounterExample.action
    IN
    /\ Cardinality(S) = 10
    /\ Cardinality(A) = 9
    /\ \A i \in 1..10 :
         \E s \in S :
            /\ s[1] = i
            /\ s[2].x = (i % 2 = 0)
    /\ \A a \in A : a[2].name = "Next"
==================================================================
