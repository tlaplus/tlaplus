---
title: TLC Configuration File (.cfg) User Manual
description: Complete guide to TLC configuration files for model checking TLA+ specifications. Learn the syntax, sections, best practices, and how to structure .cfg files to effectively configure the TLC model checker.
---

# TLC Configuration File (`.cfg`) User Manual

## Overview

A TLC configuration file (`.cfg`) specifies how the TLC model checker should check a TLA+ specification (`.tla` file). The config file defines what to check (the specification or behavior), what values to use for constants, and what properties to verify.

## Basic Structure

A `.cfg` file consists of **configuration sections**, each starting with a keyword in ALL CAPS, followed by references to formulas defined in the `.tla` file. Comments are preceded by `\*` or enclosed in `(* ... *)`.

```
SPECIFICATION Spec
CONSTANTS
    N <- MC_N
    Servers <- MC_Servers
INVARIANTS
    TypeOK
    Safety
```

## What Goes in `.cfg` vs `.tla` Files

### In `.cfg` Files (Configuration Only)
- **Which specification or behavior to check** (SPECIFICATION or INIT+NEXT)
- **References to constant definitions** (using constant replacement with `<-`)
- **Which properties to verify** (references to formulas defined in `.tla`)
- **Model-checking parameters** (symmetry sets, views, constraints)

### In `.tla` Files (Specification Logic)
- **All formulas and definitions** (Init, Next, invariants, properties)
- **CONSTANT and VARIABLE declarations**
- **Constant value definitions** (preferred location for model values)
- **Operators, modules, and mathematical logic**
- **Temporal formulas** (specifications like `Spec == Init /\ [][Next]_vars`)

## Configuration Sections

### 1. Specifying the Behavior to Check

You must specify what behavior TLC should check using **one** of these approaches:

#### Option A: SPECIFICATION (Recommended)
```
SPECIFICATION Spec
```
References a temporal formula from the `.tla` file (typically `Init /\ [][Next]_vars /\ Fairness`). **Accepts:** Level 3 (temporal formulas).

#### Option B: INIT + NEXT (For Safety Properties Only)
```
INIT Init
NEXT Next
```
Explicitly specifies the initial state predicate and next-state action. **INIT accepts:** Level 1 (state-level formulas). **NEXT accepts:** Level 2 (action-level formulas).

**Important limitation:** This approach only checks safety properties (invariants). It does not support fairness constraints, so temporal properties (liveness) cannot be verified. Use SPECIFICATION if you need to check temporal properties.

**Use INIT + NEXT only when:**
- You only want to check invariants (safety properties)
- You don't need to verify any temporal properties (liveness)

**Note:** You cannot use both SPECIFICATION and INIT+NEXT in the same config file.

### 2. CONSTANTS Section

Selects which constant definitions from the `.tla` file to use.

#### Constant Replacements (Recommended Approach)
Define your model values in the `.tla` file, then reference them in the `.cfg`:

**In `.tla` file:**
```tla
CONSTANTS N, Servers

MC_N == 4
MC_Servers == {s1, s2, s3}
```

**In `.cfg` file:**
```
CONSTANTS
    N <- MC_N
    Servers <- MC_Servers
```

The `<-` operator replaces a constant (or operator) with a different definition from the `.tla` file. This is useful for:
- Providing finite models of infinite sets (e.g., `Nat <- NatModel` where `NatModel == 0..5`)
- Swapping implementations for model checking
- Selecting different model sizes or configurations

#### Direct Constant Assignments (Discouraged)

While TLC allows direct value assignments in `.cfg` files:
```
CONSTANTS
    N = 4
    Servers = {s1, s2, s3}
```

**This practice is discouraged.** The `.cfg` file should contain only formula names, not TLA+ expressions. Define constants in the `.tla` file instead and use `<-` replacement in the `.cfg`.

**Plural form:** `CONSTANT` and `CONSTANTS` are equivalent. **Accepts:** Level 0 (constant-level formulas).

**Important:** All declared CONSTANTS in the `.tla` file must be assigned or replaced in the `.cfg` file (unless they have default definitions with `==`).

### 3. INVARIANTS Section

Specifies state predicates that should be true in all reachable states.

```
INVARIANTS
    TypeOK
    MutualExclusion
    ResourceMutex
```

**Plural form:** `INVARIANT` and `INVARIANTS` are equivalent. Multiple invariants can be listed on one line or separate lines. **Accepts:** Level 1 (state-level formulas).

- Each identifier must reference a formula defined in the `.tla` file
- TLC checks that each invariant holds in every reachable state
- If violated, TLC reports an error trace

### 4. PROPERTIES Section

Specifies temporal formulas that should be satisfied by all behaviors.

```
PROPERTIES
    Termination
    Liveness
    EventuallyConsistent
    ImplSpec
```

**Plural form:** `PROPERTY` and `PROPERTIES` are equivalent. **Accepts:** Level 2 (action-level) or Level 3 (temporal formulas).

- Used for liveness properties (e.g., `<>[]P`, `[]<>P`, `P ~> Q`)
- Used for action properties (e.g., `[][A]_v`)
- Used for refinement checking (e.g., `ImplSpec => AbsSpec`)
- Each identifier must reference a temporal formula from the `.tla` file
- More expensive to check than invariants

**Note:** Any invariant can also be checked as a property using the always (`[]`) operator. For example, if `Safety` is an invariant, you can define `AlwaysSafety == []Safety` in the `.tla` file and then check `AlwaysSafety` as a property. However, checking it as an INVARIANT is more efficient.

### 5. CONSTRAINTS Section

Limits the state space TLC explores by restricting states.

```
CONSTRAINTS
    StateConstraint
    SmallStates
```

**Plural forms:** `CONSTRAINT` and `CONSTRAINTS` are equivalent. **Accepts:** Level 1 (state-level formulas).

- State constraints: Boolean formulas that must be true for TLC to explore a state
- If a state violates a constraint, TLC doesn't explore it further (but doesn't report an error)
- Useful for bounding the search space (e.g., `depth < 10`, `Len(queue) < 5`)

### 6. ACTION_CONSTRAINT Section

Limits which actions (state transitions) TLC explores.

```
ACTION_CONSTRAINT
    LimitMessageSends
    NoFailureDuringRecovery
```

**Plural forms:** `ACTION_CONSTRAINT` and `ACTION_CONSTRAINTS` are equivalent. **Accepts:** Level 2 (action-level formulas).

- Checks if the action from one state to the next satisfies the formula
- If the action violates the constraint, the transition is not explored
- Useful for pruning the state space based on transitions (e.g., limiting certain types of actions, preventing message loss during specific phases)

### 7. SYMMETRY Section

Declares a symmetry set to reduce the state space.

```
SYMMETRY
    ServerSymmetry
    TxIdSymmetric
```

- References a set of permutations defined in the `.tla` file
- TLC treats symmetric states as equivalent, reducing states to explore
- Significant performance optimization for specifications with symmetric behavior
- Only use if symmetry is truly present (incorrect symmetry gives wrong results)
- **Accepts:** Level 1 (state-level formulas)

**Advanced concept:** Only use SYMMETRY if model checking takes too long and you understand symmetry reduction. Start without it and add it only when necessary for performance.

### 8. VIEW Section

Defines a state abstraction to reduce the state space.

```
VIEW
    AbstractView
```

- References a formula that maps states to a "view" (abstracted state)
- TLC considers two states equivalent if they have the same view
- Different from symmetry: explicitly defines the abstraction function
- Can dramatically reduce states but may miss errors if abstraction is too coarse
- **Accepts:** Level 1 (state-level formulas)

**Advanced concept:** Only use VIEW if model checking takes too long and you understand state abstraction. Incorrect views can cause TLC to miss errors. Start without it and add it only when necessary for performance.

### 9. ALIAS Section

Defines how to display states in error traces and state graphs.

```
ALIAS
    TraceAlias
```

- References a single record-valued formula from the `.tla` file
- The record fields become the displayed state variables in traces
- Useful for simplifying complex states or computing derived values for display
- Does not affect model checking, only visualization
- Only one alias can be specified
- **Accepts:** Level 2 (action-level formulas - supports both primed and unprimed variables)

### 10. POSTCONDITION Section

Specifies a condition that should hold at the end of model checking.

```
POSTCONDITION
    TraceAccepted
```

- References a single formula from the `.tla` file
- TLC checks if the formula holds after processing a trace
- Only one postcondition can be specified
- **Accepts:** Level 0 (constant-level formulas)

**Workaround for accessing trace states:** To reference state information in a postcondition, use `TLCExt!CounterExample` which provides access to the trace. See the TLCExt module documentation for details.

**Workaround for multiple postconditions:** Define a single formula in the `.tla` file that conjoins all your postconditions (e.g., `AllPostconditions == PostCond1 /\ PostCond2 /\ PostCond3`) and reference that.

### 11. CHECK_DEADLOCK

Controls whether TLC reports deadlocks as errors.

```
CHECK_DEADLOCK
    FALSE
```

- Default: `TRUE` (deadlocks are reported as errors)
- Set to `FALSE` if your specification intentionally reaches terminal states
- Values: `TRUE` or `FALSE`

## Complete Example (Best Practice)

**File: `MySpec.tla`**
```tla
---- MODULE MySpec ----
EXTENDS Integers, FiniteSets

CONSTANTS N, MaxVal, Servers

VARIABLES state, counter

TypeOK == 
    /\ counter \in 0..N
    /\ state \in {"idle", "working", "done"}

Init == counter = 0 /\ state = "idle"

Next == 
    \/ counter < N /\ counter' = counter + 1 /\ state' = "working"
    \/ counter = N /\ state' = "done" /\ UNCHANGED counter

Spec == Init /\ [][Next]_<<state, counter>>

Safety == counter <= N
Eventually == <>(state = "done")
=======================
```

**File: `MCMySpec.tla` (Model Checker definitions)**
```tla
---- MODULE MCMySpec ----
EXTENDS MySpec

\* Model values for model checking
MC_N == 5
MC_MaxVal == 100
MC_Servers == {s1, s2}
=============================
```

**File: `MCMySpec.cfg`**
```
SPECIFICATION Spec

CONSTANTS
    N <- MC_N
    MaxVal <- MC_MaxVal
    Servers <- MC_Servers

INVARIANTS
    TypeOK
    Safety

PROPERTIES
    Eventually

CHECK_DEADLOCK
    FALSE
```

**Note:** This example uses a separate `MCMySpec` module to keep `MySpec` pure and free of model-checking definitions. The main specification contains only abstract logic, while model-specific constants and values are isolated in the MC module. This allows `MySpec` to be reused, extended, model-checked with different configurations, and verified with other tools such as Apalache or TLAPS.

## Common Patterns

### Model Constants with Finite Sets
When your spec uses infinite sets like `Nat`, define a finite model:

**In main spec `.tla`:**
```tla
CONSTANTS Nat, N
```

**In model checker `.tla` (e.g., `MCMySpec.tla`):**
```tla
EXTENDS MySpec

MC_Nat == 0..4
MC_N == 3
```

**In `.cfg`:**
```
CONSTANTS
    Nat <- MC_Nat
    N <- MC_N
```

### Symmetry Reduction
**In main spec `.tla`:**
```tla
CONSTANTS Servers
Symmetry == Permutations(Servers)
```

**In model checker `.tla`:**
```tla
EXTENDS MySpec
MC_Servers == {s1, s2, s3}
```

**In `.cfg`:**
```
CONSTANTS
    Servers <- MC_Servers
SYMMETRY
    Symmetry
```

### Bounding Exploration
**In `.tla`:**
```tla
StateLimit == Len(messages) <= 5
```

**In `.cfg`:**
```
CONSTRAINTS
    StateLimit
```

## Tips and Best Practices

1. **Use a separate MC module:** Create `MCMySpec.tla` that extends your main spec and defines model values
2. **Keep .cfg files minimal:** Only formula references, no TLA+ expressions or value assignments
3. **Start simple:** Begin with small constant values and gradually increase
4. **Separate concerns:** Keep specification logic in `.tla`, configuration references in `.cfg`
5. **Comment your config:** Use `\*` to document why you chose specific model values
6. **Multiple configs:** Create multiple `.cfg` files for the same `.tla` to test different scenarios
7. **Naming convention:** Prefix model checker files with `MC`: `MCMySpec.cfg`, `MCMySpec.tla`
8. **Avoid direct assignments:** Use `CONSTANT N <- MC_N` instead of `N = 4` in `.cfg` files

## Advanced Tips

These techniques should only be used when model checking takes too long and you understand the implications:

1. **CONSTRAINTS:** Bound infinite state spaces with state constraints to limit exploration (e.g., `Len(queue) < 5`, `depth < 10`)
2. **SYMMETRY:** Declare symmetry sets when your specification has symmetric behavior (e.g., identical servers). This can provide massive speedups but will give wrong results if symmetry is incorrectly specified
3. **VIEW:** Define a state abstraction function to treat similar states as equivalent. This can dramatically reduce the state space but may miss errors if the abstraction is too coarse

## Formula Levels and Acceptable Constructs

TLA⁺ formulas can be classified by **levels**, reflecting the kinds of expressions and operators they contain. The levels are:

| **Level**   | **Description**                                                                                               | **Typical Contents**                                              |
| ----------- | ------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------- |
| **Level 0** | **Constant-level formulas** — built only from constants (no variables or temporal operators).                 | Constants, arithmetic, logical expressions over constants.        |
| **Level 1** | **State-level formulas** — built from *unprimed variables* (describe states).                                 | Predicates over state variables, no primed or temporal operators. |
| **Level 2** | **Action-level formulas** — built from *primed and unprimed variables* (describe transitions between states). | Actions, next-state relations.                                    |
| **Level 3** | **Temporal formulas** — built using *temporal operators* (e.g., [], <>, ~>, etc.).                               | Specifications, liveness properties.                              |

> **Degeneracy:**
>
> * Any level-0 formula is a degenerate level-1 formula.
> * Any level-1 formula is a degenerate level-2 formula.
> * Any level-2 formula is a degenerate level-3 formula.

## Summary Table

| Section | Purpose | Should Reference `.tla`? | Formula Level |
|---------|---------|-------------------|---------------|
| `SPECIFICATION` | Temporal formula to check | Yes (formula name) | 3 |
| `INIT` | Initial state predicate | Yes (formula name) | 1 |
| `NEXT` | Next-state action | Yes (formula name) | 2 |
| `CONSTANTS` | Replace constants with definitions | **Yes (use `<-` replacement)** | 0 |
| `INVARIANTS` | State predicates to verify | Yes (formula names) | 1 |
| `PROPERTIES` | Temporal properties to verify | Yes (formula names) | 2 or 3 |
| `CONSTRAINTS` | State space bounds | Yes (formula names) | 1 |
| `ACTION_CONSTRAINT` | Action space bounds | Yes (formula names) | 2 |
| `SYMMETRY` | Symmetry reduction | Yes (permutation set) | 1 |
| `VIEW` | State abstraction | Yes (formula name) | 1 |
| `ALIAS` | Trace display mapping | Yes (formula name) | 2 |
| `POSTCONDITION` | End-of-trace condition | Yes (formula name) | 0 |
| `CHECK_DEADLOCK` | Deadlock checking control | No (TRUE/FALSE only) | N/A |

> **Note:**
>
> * `PROPERTY` may accept formulas of level 2 (action-level) or level 3 (temporal).
> * Each lower-level formula is valid where a higher-level formula is expected, due to degeneracy.
