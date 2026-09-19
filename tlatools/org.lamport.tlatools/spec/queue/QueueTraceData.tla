--------------------------- MODULE QueueTraceData --------------------------
\* Pure data access. Java overrides load JFR; no queue semantics live in Java.
TraceLength == 0
TraceThreads == {}
TraceWorkers == {}
BufferCapacity == 1
EventAt(i) == [action |-> "", thread |-> ""]
GroupEnd(i) == i
PreviousInGroup(i) == 0
=============================================================================
