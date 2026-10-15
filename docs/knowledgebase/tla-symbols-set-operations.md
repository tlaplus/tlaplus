---
title: Write Clearer TLA+: Prefer \union and \intersect
description: Best practices for writing readable TLA+ specifications by choosing clear set operation syntax
---
## How to Use Union and Intersection in TLA+

When writing TLA+ specifications, it's important to prioritize readability and clarity for human readers. One small but effective way to do this is by choosing the more descriptive versions of set operators.

### ✅ Preferred Syntax

- Use `\union` instead of `\cup`
- Use `\intersect` instead of `\cap`

These forms are more readable because they explicitly spell out the operations, making the specification more approachable—especially for readers less familiar with mathematical shorthand.

### ❌ Avoid (Though Valid)

- `\cup` (valid TLA+ for union, but less readable)
- `\cap` (valid TLA+ for intersection, but less readable)

### Why This Matters

While both forms are syntactically correct in TLA+, most human readers find `\union` and `\intersect` easier to understand at a glance. This aligns with how people naturally verbalize these operations ("union" and "intersection"), which can aid both comprehension and collaboration.

### Example

```tla
A \union B     \* Preferred
A \intersect B \* Preferred

A \cup B       \* Avoid
A \cap B       \* Avoid
```

### Summary

| Operation    | Preferred    | Avoid  |
| ------------ | ------------ | ------ |
| Union        | `\union`     | `\cup` |
| Intersection | `\intersect` | `\cap` |

Choose clarity—use `\union` and `\intersect` in your TLA+ specs.
