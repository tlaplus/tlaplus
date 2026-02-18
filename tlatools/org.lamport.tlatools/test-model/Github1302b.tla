---- MODULE Github1302b ----
EXTENDS TLC

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

\* Without the bugfix: DOMAIN y = {<<1>>}, S = {<<1>>, <<2>>}
Inv == PrintT(<<DOMAIN y, S>>) /\ DOMAIN y # S

=====
----- CONFIG Github1302b ----
INIT Init
NEXT Next
INVARIANT Inv
========
