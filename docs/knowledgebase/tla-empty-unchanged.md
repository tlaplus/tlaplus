---
title: The Empty UNCHANGED Operator
description: Understanding the empty UNCHANGED operator in TLA+
---

In TLA+, the `UNCHANGED` operator is used to specify that certain variables do not change across a state transition. For example:

```tla
UNCHANGED << x, y >>
```

is shorthand for:

```tla
<< x, y >>' = << x, y >>
```

This means that both `x` and `y` retain their values between the current state and the next state.

---

## The empty `UNCHANGED`

Occasionally, you might see (or accidentally write) the expression:

```tla
UNCHANGED << >>
```

This expands to:

```tla
<< >>' = << >>
```

Since `<< >>` is the empty tuple, it contains no declared variables. By definition, the empty tuple is always equal to itself across states. Therefore, the expression is **always `TRUE`** and contributes nothing to the specification.

---

## Why this matters

* `UNCHANGED <<>>` has no semantic effect and can be omitted without changing the meaning of the specification.
* If it appears in your spec, it is usually a byproduct of:

  * Copy–pasting a template that lists variables in `UNCHANGED` and forgetting to fill them in.
  * Generating code from a tool that doesn’t check for empty tuples.
  * Removing variables from a conjunct without cleaning up the `UNCHANGED`.

---

## Best practice

* **Avoid leaving `UNCHANGED <<>>` in your spec.** It adds no information and can distract readers.
* If you need a placeholder in a definition where you may later add variables, it is clearer to use `TRUE` explicitly:

```tla
Next == \/ Action1
        \/ Action2
        \/ TRUE   \* placeholder for future actions
```

---

## Example

```tla
VARIABLE x

Init == x = 0

Next ==
  \/ x' = x + 1
  \/ UNCHANGED << >>
```

Here, the second disjunct (`UNCHANGED <<>>`) is equivalent to `TRUE`. Thus, `Next` allows *any state* (since the `TRUE` disjunct always holds), which is almost certainly not the intended behavior. Removing it clarifies the specification.

---

## Summary

* `UNCHANGED <<>>` = `TRUE`
* It expresses nothing about the system and should be removed.
* If you encounter it, check whether it was meant to constrain variables but was left empty by mistake.
