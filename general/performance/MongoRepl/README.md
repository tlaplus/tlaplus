# This is a snapshot of the repository at https://github.com/visualzhou/mongo-repl-tla from which we copied the spec for TLC performance testing! We claim no authorship of this specification.
---------------------------


This is an attempt to model a simplified part of the replication system of MongoDB in TLA+.

## Spec
MongoDB secondaries pull oplogs from any nodes that have more up-to-date oplogs, which is different than the push model in Raft. This spec models the gossip protocol with two synchronized actions: AppendOplog and RollbackOplog.

The spec also simplifies the election protocol. Every election will succeed in one shot, including sending and replying vote requests and learning the new term.

## Model Checking
I have successfully run model checker on the spec with a small model that has:
- 3 nodes (symmetrical model value)
- Term up to 3
- # of logs up to 10

State constraint:
```
/\ \forall i \in Server: globalCurrentTerm <= 3
/\ \forall i \in Server: Len(log[i]) <= 10
```
Invarients to check:
- NeverRollbackCommitted

The model checker generates 7778 distinct states and passes.

## Play with the Spec
To play with the spec, you may comment out Line 112 in RollbackCommitted action, which specifies that an oplog entry replicated to the majority nodes only **in the current term** can be considered as "committed". Otherwise, secondaries syncing from the the old primary will report the commit level to the old primary even though they have voted for the new primary. This differs from the Raft protocol. In Raft, voting for a new primary implies not accepting any logs from old leaders.

Commenting out Line 112 will cause the model checker to fail, giving a simple concrete failure case.

1. Node 1 becomes the primary in term 2 and writes [index: 1, term: 2] to its oplog.
2. Node 3 wins an election in term 3 without the oplog on Node 1 and writes [index: 1, term: 3].
3. Node 2 replicates [index: 1, term: 2] from Node 1, making this oplog entry replicated on the majority nodes, but it will be rolled back after syncing from Node 3.

## Conclusion
We have found the exact same issue in MongoDB code. [SERVER-22136](https://jira.mongodb.org/browse/SERVER-22136) tracks the fix to notify the old primary of the new term. We've never encountered this issue in testing or in the field and only found it by reasoning about the edge cases. This shows writing and model checking TLA+ specs is an excellent alternative way to find and verify edge cases.
