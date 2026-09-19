------------------------ MODULE DiskStateQueueTrace ------------------------
EXTENDS DiskStateQueueEvents, QueueTraceData

VARIABLE pos, used

TraceInit == Init /\ pos = 1 /\ used = {}

\* Equal timestamps leave cross-thread order unknown. The existential choice
\* below lets TLC explore orders within the earliest unconsumed timestamp group,
\* preserving each thread's sequence order and requiring Observe to permit each
\* action. The entire group must be consumed before moving to the next timestamp.
\* _POSSIBLE TraceComplete requires one spec-consistent ordering to consume the
\* whole recording, not every possible ordering. This establishes compatibility with
\* the recorded partial order, not which tied-event order actually ran in Java.
TraceNext ==
    /\ pos <= TraceLength
    /\ \E i \in (pos .. GroupEnd(pos)) \ used:
        /\ PreviousInGroup(i) = 0 \/ PreviousInGroup(i) \in used
        /\ LET event == EventAt(i)
           IN Observe(event.thread, event.action)
        /\ IF used \cup {i} = pos .. GroupEnd(pos)
           THEN pos' = GroupEnd(pos) + 1 /\ used' = {}
           ELSE pos' = pos /\ used' = used \cup {i}

\* The configuration requires a reachable state where the whole recording is consumed.
TraceComplete == pos > TraceLength
=============================================================================
