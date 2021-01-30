------------- CONFIG TLCExtTrace ---------

SPECIFICATION Spec
INVARIANT Inv
INVARIANT InvTraceFrom
===================

---- MODULE TLCExtTrace ----

EXTENDS Integers, TLCExt, Sequences

VARIABLE x

Spec == x = 1 /\ [][x < 10 /\ x' = x + 1]_x

\* Assert that Trace is the sequence of states up to the current value of x.
Inv == /\ Len(Trace) = x
       /\ \A i \in 1..x : Trace[i].x = i /\ DOMAIN Trace[i] = {"x"}
       
       
InvTraceFrom == \A i \in 1..x : 
                   /\ Len(TraceFrom([x |-> i])) = x - i + 1
                   /\ \A j \in 1..Len(TraceFrom([x |-> i])) : 
                         /\ TraceFrom([x |-> i])[j].x = i + j - 1
==================================
