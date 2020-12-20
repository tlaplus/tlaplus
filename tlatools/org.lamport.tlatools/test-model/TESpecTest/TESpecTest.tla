---------- MODULE TESpecTest -----------

EXTENDS Naturals

CONSTANT Limit

ASSUME Limit \in Nat

VARIABLES x, y

Safety ==
    /\ x /= Limit

Liveness ==
    /\ <>(x = Limit)

Init ==
    /\ x = 0
    /\ y = FALSE

Increment ==
    /\ x' = x + 1
    /\ y' = ~y

Decrement ==
    /\ x > 0
    /\ x' = x - 1
    /\ y' = ~y

Next ==
    \/ Increment
    \/ Decrement

Spec ==
    /\ Init
    /\ [][Next]_<<x, y>>

LiveSpec ==
    /\ Init
    /\ [][Next]_<<x, y>>
    /\ WF_<<x, y>>(Increment)

EqAlias ==
    [x |-> x,
    y |-> y]

MapAlias ==
    [x |-> x + 1,
    y |-> ~y]

SupersetAlias ==
    [x |-> x,
    y |-> y,
    z |-> ~y]

SubsetAlias ==
    [x |-> x]

==============================================
