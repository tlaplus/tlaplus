---
title: Functions, Records, and Sequences in TLA+
description: A comprehensive guide to functions in TLA+, including how to define and modify them, and understanding records and sequences as special cases of functions.
---

## Functions, Records, and Sequences in TLA+

In TLA+, **functions** are fundamental data structures that map values from a **domain** to a **codomain** (also called range). If you come from a programming background, think of functions as **maps**, **dictionaries**, or **associative arrays**.

> 🧠 Unlike operators, functions are *first-class values* in TLA+—they can be stored in variables, passed as arguments, and quantified over.

---

### 🔧 Defining Functions

A function is defined using the **mapsto** syntax: `[x \in S |-> expr]`

```tla
\* A function that doubles each natural number
double == [n \in Nat |-> 2 * n]

\* A function mapping people to their ages
ages == [p \in {"Alice", "Bob", "Carol"} |-> 
            IF p = "Alice" THEN 30
            ELSE IF p = "Bob" THEN 25
            ELSE 28]
```

**Accessing function values** uses square bracket notation:

```tla
double[5]          \* Evaluates to 10
ages["Alice"]      \* Evaluates to 30
```

You can retrieve a function's domain with `DOMAIN`:

```tla
DOMAIN ages        \* Evaluates to {"Alice", "Bob", "Carol"}
```

---

### 📐 Set of All Functions: `[A -> B]`

TLA+ provides syntax to define the **set of all functions** from domain `A` to codomain `B`:

```tla
[A -> B]
```

This is the set of *all possible* functions that map every element of `A` to some element of `B`.

#### Example

```tla
\* All functions from {1, 2} to {TRUE, FALSE}
AllMappings == [{1, 2} -> {TRUE, FALSE}]

\* This set contains 4 functions:
\*   [1 |-> TRUE,  2 |-> TRUE ]
\*   [1 |-> TRUE,  2 |-> FALSE]
\*   [1 |-> FALSE, 2 |-> TRUE ]
\*   [1 |-> FALSE, 2 |-> FALSE]
```

> 💡 The size of `[A -> B]` is `|B|^|A|` (cardinality of B raised to cardinality of A).

---

### ✏️ Modifying Functions with `EXCEPT`

Since TLA+ is mathematical, you don't "mutate" a function. Instead, you create a **new function** based on an existing one using `EXCEPT`.

```tla
\* Original function
ages == [p \in {"Alice", "Bob"} |-> 
            IF p = "Alice" THEN 30 ELSE 25]

\* New function with Bob's age updated
ages2 == [ages EXCEPT !["Bob"] = 26]
```

After this, `ages2["Bob"]` evaluates to `26`, while `ages["Bob"]` remains `25`.

#### Using `@` to Reference the Old Value

The special symbol `@` refers to the **previous value** at that position:

```tla
\* Increment Alice's age by 1
ages3 == [ages EXCEPT !["Alice"] = @ + 1]
\* ages3["Alice"] is now 31
```

#### Multiple Updates

You can update multiple keys in a single `EXCEPT`:

```tla
ages4 == [ages EXCEPT !["Alice"] = 31, !["Bob"] = 26]
```

#### Nested Function Updates

For functions of functions (nested structures), use chained `!` notation:

```tla
\* A nested structure: departments -> employees -> salaries
company == [dept \in {"Engineering", "Sales"} |->
              [emp \in {"Alice", "Bob"} |-> 50000]]

\* Give Alice in Engineering a raise
company2 == [company EXCEPT !["Engineering"]["Alice"] = 75000]
```

> ⚠️ **Performance Note:** TLA+ is mathematics, not a programming language. Using `EXCEPT` does not "efficiently update" a function—it defines an entirely new function. There is no computational advantage to using `EXCEPT` over defining a fresh function. However, `EXCEPT` is often *clearer* and more concise.

---

### 🔄 Recursive Functions

TLA+ allows defining functions that refer to themselves using the **recursive function definition** syntax:

```tla
f[x \in S] == expr   \* where expr may reference f
```

This is distinct from recursive *operators* (which use the `RECURSIVE` keyword). A recursive function definition creates a function value that can reference itself.

#### Example: Factorial

```tla
factorial[n \in Nat] == IF n = 0 THEN 1 ELSE n * factorial[n - 1]
```

Here, `factorial` is a function from `Nat` to `Nat` that refers to itself in its definition.

#### Example: Fibonacci

```tla
fib[n \in Nat] == IF n <= 1 THEN n ELSE fib[n - 1] + fib[n - 2]
```

#### Example: Sum of a Sequence

```tla
EXTENDS Sequences, Naturals

\* Sum elements of a sequence (using indices)
sum[s \in Seq(Nat)] == 
    IF s = <<>> THEN 0 
    ELSE Head(s) + sum[Tail(s)]

\* sum[<<1, 2, 3>>] evaluates to 6
```

#### Multiple Parameters

For functions with multiple parameters, use a tuple or record as the domain:

```tla
\* Power function using a tuple domain
power[pair \in Nat \X Nat] == 
    LET base == pair[1]
        exp  == pair[2]
    IN IF exp = 0 THEN 1 ELSE base * power[<<base, exp - 1>>]

\* power[<<2, 3>>] evaluates to 8
```

> 💡 **Tip:** Many recursive patterns over sequences and sets can be expressed more elegantly using operators from the `Folds` community module, such as `FoldSeq` and `FoldSet`.

---

### 📜 Sequences: Functions with Natural Number Domains

**Sequences** are functions whose domain is `1..n` (the set `{1, 2, ..., n}`) for some natural number `n`. They represent ordered lists.

#### Defining Sequences

```tla
EXTENDS Sequences

\* A sequence of three elements
colors == <<"red", "green", "blue">>

\* Equivalent to:
colors == [i \in 1..3 |-> 
              IF i = 1 THEN "red"
              ELSE IF i = 2 THEN "green"
              ELSE "blue"]
```

#### Accessing Elements

```tla
colors[1]          \* Evaluates to "red"
colors[2]          \* Evaluates to "green"
Len(colors)        \* Evaluates to 3
DOMAIN colors      \* Evaluates to {1, 2, 3}
```

> ⚠️ Sequences are **1-indexed**, not 0-indexed!

#### Set of All Sequences

```tla
\* All sequences of elements from set S
Seq(S)

\* Example: all sequences of bits
Seq({0, 1})        \* Contains <<>>, <<0>>, <<1>>, <<0,0>>, <<0,1>>, ...
```

> Note: `Seq(S)` is an *infinite* set (for non-empty `S`), so TLC cannot enumerate it directly. Use bounded versions like `BoundedSeq(S, n)` from SequencesExt.

---

### 📦 Records: Functions with String Domains

**Records** are simply functions whose domain is a set of strings (field names). TLA+ provides convenient syntax for working with them.

#### Defining Records

```tla
\* A record with fields "name" and "age"
person == [name |-> "Alice", age |-> 30]

\* Equivalent to:
person == [f \in {"name", "age"} |-> 
              IF f = "name" THEN "Alice" ELSE 30]
```

#### Accessing Fields

Use dot notation or bracket notation:

```tla
person.name        \* Evaluates to "Alice"
person["name"]     \* Also evaluates to "Alice"
```

#### Set of All Records

```tla
\* All possible person records
People == [name: {"Alice", "Bob"}, age: {25, 30, 35}]

\* This is the set of all records with:
\*   - "name" field from {"Alice", "Bob"}
\*   - "age" field from {25, 30, 35}
\* Contains 2 * 3 = 6 records
```

> 🔍 Note the syntax difference: `:` for record sets, `|->` for specific records.

#### Updating Records with `EXCEPT`

```tla
person2 == [person EXCEPT !.age = 31]
\* Or equivalently:
person2 == [person EXCEPT !["age"] = 31]
```

---

### 🧰 Useful Modules

TLA+ provides operations for functions and sequences across several modules:

| Module | Description |
|--------|-------------|
| `Sequences` | Standard module with basic sequence operations (`Len`, `Head`, `Tail`, `Append`, `SubSeq`, `\o`) |
| `Functions` | Community module with function utilities (`Range`, `Restrict`, `Inverse`, injections, surjections, bijections) |
| `SequencesExt` | Community module with extended sequence operations (`ToSet`, `SetToSeq`, `Reverse`, `FlattenSeq`, `BoundedSeq`) |
| `Folds` | Community module with fold operations over sequences and sets (`FoldSeq`, `FoldSet`) |

#### How to Explore Module Contents

**In VS Code / Cursor:** Add an `EXTENDS` statement and Ctrl+Click (Cmd+Click on macOS) on the module name to navigate to its source:

```tla
EXTENDS Sequences, Functions, SequencesExt
```

**On the web:** Browse the standard modules at [github.com/tlaplus/tlaplus](https://github.com/tlaplus/tlaplus/tree/master/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules) and CommunityModules at [github.com/tlaplus/CommunityModules](https://github.com/tlaplus/CommunityModules/tree/main/modules).

**For AI assistants:** Use the TLA+ MCP tools `tlaplus_mcp_sany_modules` to list available modules, and `tlaplus_mcp_sany_symbol` to extract symbols from a specific module.

---

### 🧠 Summary

| Concept | Domain | Syntax | Access |
|---------|--------|--------|--------|
| **Function** | Any set | `[x \in S \|-> expr]` | `f[x]` |
| **Sequence** | `1..n` | `<<e1, e2, ...>>` | `s[i]` (1-indexed) |
| **Record** | Strings | `[field1 \|-> v1, ...]` | `r.field` or `r["field"]` |

| Set of... | Syntax |
|-----------|--------|
| All functions A → B | `[A -> B]` |
| All sequences | `Seq(S)` |
| All records | `[field1: S1, field2: S2, ...]` |

> 🎯 **Key Insight:** Records and sequences are not special types—they're just functions with specific domains. This unification is a hallmark of TLA+'s elegant mathematical foundation.
