---
title: Operators vs. Functions in TLA+: Key Differences
description: Learn the distinction between operators and functions in TLA+. Operators act like macros that expand into expressions, while functions are first-class mappings from inputs to outputs. This guide explains their definitions, usage, evaluation, and examples to help you apply them correctly in specifications.
---

## Operators vs. Functions in TLA+: Key Differences

The distinction between **functions** and **operators** in **TLA+**.

### 🔧 **Rule**
>
> **Operators** in TLA+ are symbolic or named expressions that *take arguments and produce expressions*.  
> **Functions** are mappings from a *domain* to a *range*, where each input in the domain maps to exactly one output.

---

### 🧠 Think of it like this

| Concept          | Operators                                                               | Functions                                                         |
|------------------|-------------------------------------------------------------------------|-------------------------------------------------------------------|
| **Nature**       | Logical/mathematical *expression*                                       | *Data structure* mapping inputs to outputs                        |
| **Usage**        | Used like a *macro* or expression generator                             | Used like a value or variable                                     |
| **Input**        | Passed explicitly via parentheses (`F(x, y)`)                           | Accessed via function application (`f[x]`)                        |
| **Definition**   | Via `==`, e.g., `F(x) == x + 1`                                         | Via `[x ∈ S ↦ expr]`, e.g., `f == [x ∈ S ↦ x + 1]`                |
| **Evaluation**   | Substitutes and evaluates as a formula                                  | Evaluates to a value (a function object)                          |
| **Higher-order** | Not directly first-class (can be passed around but not quantified over) | First-class citizens (can be stored, passed, and quantified over) |

---

### ✅ Examples

#### 1. **Operator**

```tla
Double(x) == 2 * x
```

- `Double(3)` evaluates to `6`
- Think of `Double` as a macro that expands into `2 * x`.

#### 2. **Function**

```tla
f == [x ∈ Nat ↦ 2 * x]
```

- `f[3]` evaluates to `6`
- `f` is a value — a mapping from `Nat` to results.

---

### ✨ Summary Shortcut
>
> **Operators** are like macros that compute expressions.  
> **Functions** are values that map inputs to outputs.
