---- MODULE Github1302 ----
r == [ i \in {1} |-> "A"]

\* Changing this to {r} prevents the bug:
\* {r} is a SetEnumValue but not FcnLambdaValue.
S == [ {1} -> {"A"} ]

ASSUME S = {r}

VARIABLES v

TypeOK == v \in [S -> {1}]

Init == v = [s \in S |-> 1]

\* This is equivalent to UNCHANGED v.
Next == v' = [v EXCEPT ![ r ] = @]

Spec == Init /\ [][Next]_v /\ WF_v(Next)

\* The actual property doesn't matter here as long
\* as it triggers the simulator's liveness checker.
Prop == TRUE ~> TRUE

=====
----- CONFIG Github1302 ----
SPECIFICATION Spec

PROPERTY Prop

\* Checking the invariant causes TLC to correctly
\* report stuttering.
\* Hypothesis: Invariant checking causes FcnLambdaValue
\* to be converted before liveness checking.
\*INVARIANT TypeOK
========