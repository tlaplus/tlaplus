---
title: Preventing spec bugs with *Locality* properties in TLA+ Specifications
description: How to use locality properties to prevent accidental concurrent state changes in TLA+ specifications. Locality properties guard against bugs where actions incorrectly modify multiple processes' local state in a single action.
---

## Locality properties in TLA+ Specifications

### The Challenge: Global Variables in Distributed Models

In TLA+, **all variables are global**. When modeling distributed systems, we typically use a single variable (often a function) to represent the local state of multiple processes. For example:

```tla
VARIABLES nodeState   \* nodeState[n] is the local state of process n

Init == nodeState = [n \in Nodes |-> InitialState]
```

This modeling approach makes reasoning about the system simple, but it introduces a subtle risk: **nothing prevents an action from accidentally modifying the state of multiple processes simultaneously**.

---

### 🔀 When Multi-Process Updates Are Legitimate

Before introducing safeguards, it's important to recognize that **some actions legitimately modify multiple components**. A classic example is message passing:

```tla
VARIABLES inbox, outbox

\* Send a message from process N to process M
Send(n, m, msg) ==
    /\ msg \in outbox[n]
    /\ outbox' = [outbox EXCEPT ![n] = @ \ {msg}]
    /\ inbox' = [inbox EXCEPT ![m] = @ \cup {msg}]
```

Here, `Send` modifies both `outbox[n]` and `inbox[m]`—this is correct because the action models a message transfer between two processes. The key insight is that `inbox` and `outbox` are **not process-local variables**; they represent communication channels that inherently involve multiple parties.

---

### 🛑 Preventing Accidental Concurrent State Changes

For variables that represent **truly local state** (state that should only be modified by actions involving that specific process), you can define a **locality property** that enforces this constraint:

```tla
CONSTANTS Procs

VARIABLES inbox, outbox, state

\* NoConcurrentStateChanges: Property ensuring process-local state changes
\* are atomic. There is no action that simultaneously changes the state of
\* two different processes. The variable state[p] is process-local and should
\* only be modified by actions involving that specific process.
\*
\* PREVENTS: Concurrency bugs where actions incorrectly modify multiple
\* processes' state simultaneously, violating the distributed nature of the
\* protocol. This catches specification errors where cross-process state
\* coupling is accidentally introduced.
NoConcurrentStateChanges ==
    [][\A p, q \in Procs:
            /\ p # q
            /\ state[p] # state'[p]
            => UNCHANGED state[q]
    ]_vars
```

This property states: "For any two distinct processes `p` and `q`, if process `p`'s local state changes, then process `q`'s local state must remain unchanged."

---

### 📖 Understanding the Property

Let's break down the structure:

```tla
[][\A p, q \in Procs:
        /\ p # q                    \* For distinct processes
        /\ state[p] # state'[p]     \* If p's state changes
        => UNCHANGED state[q]       \* Then q's state is unchanged
]_vars
```

| Component | Meaning |
|-----------|---------|
| `[][...]_vars` | This is a temporal property over all transitions |
| `\A p, q \in Procs: p # q` | For all pairs of distinct processes |
| `state[p] # state'[p]` | Process p's local state changes in this step |
| `=> UNCHANGED ...` | Implies that q's state must not change |

> ⚠️ **Note:** Locality properties only prevent *writing* to another process's state. They do not prevent *reading* it.

---

#### Group Related Process-Local Variables

When a process has multiple local variables, protect them together:

```tla
\* All of process n's local state should change atomically
NodeLocalVars(n) == <<state[n], buffer[n], timer[n]>>

NoMultiNodeLocalUpdates ==
    [][\A m, n \in Nodes:
            /\ m # n
            /\ NodeLocalVars(m) # NodeLocalVars(m)'
            => UNCHANGED NodeLocalVars(n)
    ]_vars
```

#### Add to TLC Configuration as a Property

Since this is a temporal property, add it to your TLC configuration file as a `PROPERTY`, not an `INVARIANT`:

```cfg
SPECIFICATION Spec
PROPERTY NoConcurrentStateChanges
```
