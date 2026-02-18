---- MODULE Github1302c ----
EXTENDS TLC, TLCExt

\* Non-Reducible domain so the outer function stays a lazy FcnLambdaValue.
S == [{1} -> {1, 2}]
I == [s \in S |-> 0]

r1 == [i \in {1} |-> 1]
r2 == [i \in {1} |-> 2]

fcn == r1 :> 10

VARIABLES x, y

Init ==
    /\ x = [I EXCEPT ![r1] = fcn] \* (<<1>> :> (<<1>> :> 10) @@ <<2>> :> 0)
    /\ y = [x EXCEPT ![r2] = 99]  \* (<<1>> :> (<<1>> :> 10) @@ <<2>> :> 99)

Next == UNCHANGED <<x, y>>

\* Evaluating correct from scratch creates fresh ValueExcept objects that are
\* not shared with x, so no corruption occurs.
correct == [([([s \in S |-> 0]) EXCEPT ![r1] = fcn]) EXCEPT ![r2] = 99]

Inv == TLCFP(y) = TLCFP(correct)

=====
----- CONFIG Github1302c ----
INIT Init
NEXT Next
INVARIANT Inv
========
