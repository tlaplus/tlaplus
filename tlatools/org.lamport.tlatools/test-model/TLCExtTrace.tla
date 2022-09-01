------------- CONFIG TLCExtTrace ---------

SPECIFICATION Spec
INVARIANT Inv
CONSTRAINT Inv
===================

---- MODULE TLCExtTrace ----

EXTENDS Integers, TLCExt, Sequences

VARIABLE x

Spec == x = 1 /\ [][x < 10 /\ x' = x + 1]_x

\* Assert that Trace is the sequence of states up to the current value of x.
Inv == /\ Len(Trace) = x
       /\ \A i \in 1..x : /\ Trace[i].x = i

Inv2 == x < 7

Alias ==
[
	x |-> x,
	t |-> Trace
]
==================================
