---
title: Understanding `EXTENDS` vs `INSTANCE` in TLA+
description: Learn the difference between `EXTENDS` and `INSTANCE` in TLA+, when to use each, and how they handle imports, namespacing, constants, and variables.
---

In **TLA+**, `EXTENDS` and `INSTANCE` are both used to bring in definitions from other modules, but they serve **distinct purposes**.

---

### ✅ Use `EXTENDS` to **import definitions directly**

When you `EXTEND` a module, you bring all of its public operators and definitions into your spec, as if you copied and pasted them at the top.

Example:

```tla
EXTENDS Naturals, Sequences
```

This makes operators like `+`, `<`, `Len`, `Append`, etc., available without qualification.

> Think of `EXTENDS` as syntactically *inlining* the target module. This is convenient but can lead to **name clashes**—especially if multiple modules define the same operator or constant name.

For instance, if your module already defines `Len`, and you `EXTEND Sequences`, you’ll get a conflict since both define `Len`.

---

### ✅ Use `INSTANCE` for **namespacing** or **parameterization**

#### 🔹 Namespacing: avoid name clashes

To use another module without polluting your namespace, use `INSTANCE`. This lets you qualify all referenced operators with an instance label.

Example:

```tla
---- MODULE YourSpec ----
S == INSTANCE Sequences

Len(cars) ==
    S!Len(cars) + 1
```

Now `S!Len` refers to the `Len` from `Sequences`, and your own `Len` is unaffected.

---

#### 🔹 Parameterization: substitute `CONSTANTS` and `VARIABLES`

If a module declares `CONSTANTS`, you may want to use `INSTANCE` to provide values via `WITH`. The same applies if the module declares `VARIABLES`: in that case, you must map those variables to expressions or variables from your own module. This is also known as a **refinement mapping**.

So, `WITH` lets you:

- Provide values for declared `CONSTANTS`
- Define how the instantiated module's `VARIABLES` correspond to your module's state

---

#### Example

```tla
---- MODULE Stack ----
CONSTANT Elem
VARIABLES stack

Init == stack = << >>
Push(x) == stack' = Append(stack, x)
Pop == stack' = Head(stack)
Next == \E x \in Elem: Push(x) \/ Pop
====
```

To use `Stack`, you’d write:

```tla
EXTENDS Sequences
INSTANCE Stack WITH Elem <- {1, 2, 3}, stack <- s
```

This gives you:

- Access to `Init`, `Push`, `Pop`, `Next` from `Stack`
- With:
  - `Elem` replaced by `{1, 2, 3}`
  - `stack` mapped to your own module’s variable `s`

> 🔁 This makes it possible to **reuse behavior** across modules while plugging in different constant values and state variables.

You can also create **multiple instances** of the same module with different parameters:

```tla
S1 == INSTANCE Stack WITH Elem <- {1, 2}, stack <- s1
S2 == INSTANCE Stack WITH Elem <- {"a", "b"}, stack <- s2
```

---

### TL;DR

| Use Case                        | Use `EXTENDS`                 | Use `INSTANCE`                                       |
|--------------------------------|-------------------------------|------------------------------------------------------|
| Bring in standard definitions  | ✅ Yes                         | ✖ Not typical                                        |
| Avoid name clashes             | ✖ Risk of conflict            | ✅ Use qualified access (`M!Op`)                     |
| Module has `CONSTANTS`         | ✖ Not allowed                 | ✅ Use `WITH` to provide values                      |
| Module has `VARIABLES`         | ✖ Not allowed                 | ✅ Map to local variables (refinement)               |
| Multiple versions with config  | ✖ Not possible                | ✅ Each instance can use different substitutions     |
