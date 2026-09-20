---------------------- MODULE MCDiskStateQueueWorkload ----------------------
EXTENDS DiskStateQueueWorkload

\* TLC exploration bound, not a restriction on workload actions.
CONSTANT MaxQueueLoad

ASSUME QueueLoadAssumption == /\ MaxQueueLoad \in Nat
                              /\ MaxQueueLoad >= Capacity + 1

\* Bound total queue occupancy, including disk pools. Each worker dequeues at
\* most once, so this also bounds total insertions and pool file indices here.
\* Repeated dequeue/enqueue cycles would require a separate abstraction of the
\* monotonically increasing file indices.
QueueLoadBound == Size(queue) <= MaxQueueLoad

\* QueueLoadBound truncates executions; the TLC configuration checks safety only.
=============================================================================
