---
title: Avoid Combining Invariants in TLA+ for Clearer TLC Error Reporting
description: When writing TLA+ specifications, avoid grouping multiple invariants into a single conjunctive expression. TLC will only report the composite failure, making it unclear which condition was violated. Instead, list each invariant separately in your TLC configuration so that errors are reported precisely, simplifying debugging and analysis.
---
### ⚠️ **Avoid Combining Invariants in TLA+**

When writing TLA+ specifications, **do not combine multiple invariants into a single conjunctive (`/\`) expression** and then refer to that composite in your TLC configuration. If you do, **TLC will only report that the combined invariant was violated**, without indicating which specific component failed.

For example, the following is discouraged:

```tla
TypeOK ==
  /\ queue \in Seq(Nat)
  /\ waitingProducers \subseteq Producers
  /\ waitingConsumers \subseteq Consumers

DeadlockFreedom ==
  waiting # (Producers \cup Consumers)

QueueBounded ==
  Len(queue) <= QCapacity

Inv ==
  /\ TypeOK
  /\ DeadlockFreedom
  /\ QueueBounded
```

TLC config file:

```cfg
INVARIANT Inv
```

If any of the conditions fail (e.g., `QueueBounded` is violated), TLC will only indicate that `Inv` is violated—not which specific part.

---

### ✅ **Recommended Approach: List Invariants Separately**

Instead, **declare each invariant individually** and reference each one by name in the TLC configuration. This allows TLC to pinpoint exactly which invariant failed.

```tla
TypeOK ==
  /\ queue \in Seq(Nat)
  /\ waitingProducers \subseteq Producers
  /\ waitingConsumers \subseteq Consumers

DeadlockFreedom ==
  waiting # (Producers \cup Consumers)

QueueBounded ==
  Len(queue) <= QCapacity
```

TLC config file:

```cfg
INVARIANTS
  TypeOK
  DeadlockFreedom
  QueueBounded
```

This way, TLC will clearly report which specific invariant(s) failed, making debugging much easier.
