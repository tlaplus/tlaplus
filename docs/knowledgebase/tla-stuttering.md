---
title: How to Model Stuttering in TLA+
description: How to Model Stuttering in TLA+
---

## How to Model Stuttering in TLA+

### What is Stuttering?

In TLA+, a *stuttering step* is a step in which the system's variables do not change. Stuttering steps are important in temporal logic because they allow behaviors to be extended with 'do nothing' steps, making specifications robust to timing and implementation details.

### Stuttering is Built-In

You **do not need to explicitly model stuttering steps** in TLA+. The temporal formula `[Next]_vars` automatically allows for stuttering: it is equivalent to `Next \/ vars' = vars`. This means that, at every step, the system can either take a `Next` step or do nothing (a stuttering step).

### Example: Stuttering in Action

Suppose you have a system with two actions, `A` and `B`. You might be tempted to add an explicit `Skip` action for stuttering, but this is unnecessary:

```tla
VARIABLES vars

A == \* ... some action ...
B == \* ... another action ...

Skip ==
    UNCHANGED vars

Next ==
    \/ A
    \/ B
    \* No need to add: \/ Skip

Spec == Init /\ [][Next]_vars
```

Here, `[Next]_vars` means that at each step, either `Next` occurs (i.e., `A` or `B`), **or** the variables remain unchanged (a stuttering step). You do not need to define a separate `Skip` or `UNCHANGED vars` action.

### Best Practices

- **Never add explicit stuttering steps** (like `Skip == UNCHANGED vars`) unless you have a very specific reason.
- Use `[Next]_vars` in your temporal formulas to get stuttering insensitivity for free.
- Remember: all TLA+ behaviors are stuttering insensitive by default when using `[Next]_vars`.

### Summary

Stuttering steps are automatically included in TLA+ specifications via the `[Next]_vars` notation. You almost never need to model them explicitly. This makes your specs simpler and more robust.
