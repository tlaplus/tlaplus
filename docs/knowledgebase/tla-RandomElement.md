---
title: RandomElement vs. Non-Determinism
description: Understanding the RandomElement operator in TLA+
---

## How To: Non-Determinism vs. RandomElement in TLA+

When modeling systems in TLA+, we frequently need to express that a system can make arbitrary choices—such as picking any element from a set, or taking one of several possible actions. This is called **non-determinism**. TLA+ natively supports non-determinism through its logical operators and set constructs. For example, the following action allows `x` to take any value from the set `S`:

```tla
x' \in S
```

This means that in the next state, `x` can be any element of `S`. The model checker (TLC) will explore all possible choices for `x` in its analysis.

### The RandomElement Operator

You may notice that the TLC module defines an operator called `RandomElement`. This operator is **rarely used** in TLA+ modeling. In fact, in almost all cases, you should **not** use `RandomElement` when expressing non-deterministic choices. Instead, rely on TLA+'s built-in non-determinism as shown above.

#### Why Not Use RandomElement?

- **Non-determinism is the norm:** TLA+ is designed to model all possible behaviors, not to simulate random or probabilistic choices.
- **Clarity and correctness:** Using non-deterministic constructs makes your specification clearer and ensures that all possible behaviors are considered.

### Niche Use Cases

The use of `RandomElement` is so rare and specialized that this howto does **not** document its niche applications. If you think you need `RandomElement`, reconsider your approach—there is almost always a better way to model your system using TLA+'s standard non-deterministic constructs.

**Summary:**  
When modeling in TLA+, always use non-determinism (e.g., `x' \in S`) to express arbitrary choices. Do **not** use `RandomElement`—its use is almost never appropriate in system specifications.