---
title: How to debug INVARIANT or PROPERTY Violations
description: A practical guide to debugging TLC model checking errors, focusing on strategies for diagnosing invariant and property violations. It outlines how to minimize configurations, verify invariants, and systematically isolate root causes of property failures.
---

## How to debug INVARIANT or PROPERTY Violations

### Debugging and Diagnosing INVARIANT or PROPERTY Violations

When you encounter an invariant or property violation, start by **minimizing the TLC configuration**. Simplify the model as much as possible—reduce constants, constraints, and the state space—to identify the smallest configuration that still triggers the violation. This helps isolate the root cause more effectively.

### Debugging and Diagnosing PROPERTY Violations

Before analyzing a `PROPERTY` violation, ensure your specification includes a sufficient set of invariants and that all of them hold.

To verify this:

1. Temporarily **remove the `PROPERTY` (or `PROPERTIES`) entries** from your TLC configuration.
2. Rerun the model checker to check only the invariants.

If any invariant fails, address that issue first. This step helps determine whether the `PROPERTY` violation stems from a more fundamental problem in the model, rather than the property itself.
