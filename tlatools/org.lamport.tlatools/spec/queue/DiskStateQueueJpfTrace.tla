--------------------- MODULE DiskStateQueueJpfTrace -------------------------
EXTENDS DiskStateQueueEvents, QueueJpfData, TLC

ASSUME JpfNodeCount > 0

VARIABLE node

JpfInit ==
    /\ Init /\ node = 0
    /\ TLCSet(0, {0})

JpfNext ==
    \E child \in JpfChildren(node):
        /\ LET event == JpfEvent(child)
           IN Observe(event.thread, event.action)
        /\ node' = child

\* Each node identifies one recorded execution prefix. All must be reachable,
\* each through at least one specification behavior prefix. Reaching just one
\* leaf is insufficient. Keep the reached set outside fingerprints; use one worker.
RememberNodes == TLCSet(0, TLCGet(0) \cup {node})
AllNodesReplayed == TLCGet(0) = 0..JpfNodeCount

JpfAlias == [node |-> node, next |-> {JpfEvent(n): n \in JpfChildren(node)},
             queue |-> queue, owner |-> owner, counted |-> counted, pc |-> pc,
             waiters |-> waiters, finish |-> finish, stop |-> stop]
=============================================================================
