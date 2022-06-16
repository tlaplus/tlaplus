\* Copyright (c) 2022, Oracle and/or its affiliates.

---- MODULE Github702 ----
\* Previously, TLC would fail with
\*  > In computing next states, TLC found the identifier
\*  > fizzbuzz undefined in an UNCHANGED expression

EXTENDS Naturals
VARIABLES y, z

fizzbuzz == 1
INSTANCE x_unchanged WITH
    x <- fizzbuzz

====

---- MODULE x_unchanged ----

EXTENDS Naturals

VARIABLES x, y, z

Init ==
    /\ x \in {1,2,3}
    /\ y \in {1,2,3}
    /\ z \in {1,2,3}

Next ==
    /\ y < 10
    /\ y' = y + 1
    /\ UNCHANGED <<x, z>>

Spec == Init /\ [][Next]_<<x, y, z>>

====
