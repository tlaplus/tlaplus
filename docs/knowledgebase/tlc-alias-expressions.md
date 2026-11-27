---
title: TLC ALIAS Expressions for Trace Analysis
description: Learn how to use ALIAS expressions in TLC configuration files to customize error trace output by filtering variables, computing derived values, and formatting traces for analysis tools.
---

# TLC ALIAS Expressions for Trace Analysis

## Overview

The `ALIAS` feature in TLC allows you to customize how error traces and behaviors are displayed. By defining an `ALIAS` expression in your TLC configuration file, you can:

- **Filter variables**: Show only relevant state variables, hiding implementation details
- **Rename variables**: Use more descriptive names in traces
- **Compute derived values**: Display compound values computed from state variables
- **Pretty print complex values**: Format complex data structures for readability
- **Add debugging information**: Include trace metadata and enablement predicates
- **Support trace analysis tools**: Format output for external visualization tools

ALIAS expressions are evaluated on every step (pair of states `s -> t`) in a behavior. When TLC prints an error trace, it evaluates the ALIAS expression and displays the result instead of the raw state.

## How ALIAS Works

### Evaluation Model

An ALIAS expression is evaluated on each **transition** (pair of states) in an error trace:
- **`s`**: The current state (unprimed variables)
- **`t`**: The next state (primed variables)

The ALIAS expression can reference both unprimed and primed variables, making it an **action-level formula** (Level 2).

### Display Behavior

TLC displays the result of the ALIAS expression **in place of state `s`**. The result should be a **record** where each field becomes a displayed variable in the trace.

If evaluating the ALIAS expression fails for any step, TLC falls back to displaying the full state `s`.

## Basic Usage

### Configuration File Setup

Add the `ALIAS` keyword to your `.cfg` file:

```
SPECIFICATION Spec
INVARIANT Inv
ALIAS Alias
```

### Defining an ALIAS Expression

In your `.tla` file, define `Alias` as a record-valued expression:

```tla
Alias == [
    var1 |-> x,
    var2 |-> y,
    computed |-> x + y
]
```

## Complete Example

### Specification File

```tla
---- MODULE Counter ----
EXTENDS Integers

VARIABLE count
vars == <<count>>

Init == count = 0

Increment == count' = count + 1

Next == Increment

Spec == Init /\ [][Next]_vars

Inv == count < 5

\* ALIAS expression for trace customization
Alias == [
    counter |-> count,
    isEven |-> count % 2 = 0,
    nextEnabled |-> ENABLED Increment
]
=======================
```

### Configuration File

```
SPECIFICATION Spec
INVARIANT Inv
ALIAS Alias
```

### Trace Output

With the ALIAS defined above, when TLC finds an invariant violation at `count = 5`, it displays:

```
Error: Invariant Inv is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ counter = 0
/\ isEven = TRUE
/\ nextEnabled = TRUE

State 2: <Increment>
/\ counter = 1
/\ isEven = FALSE
/\ nextEnabled = TRUE

State 3: <Increment>
/\ counter = 2
/\ isEven = TRUE
/\ nextEnabled = TRUE

...

State 6: <Increment>
/\ counter = 5
/\ isEven = FALSE
/\ nextEnabled = TRUE
```

Notice how:
- Variables appear in the order specified in the ALIAS record
- Computed values (`isEven`) are displayed alongside state variables
- The trace is more readable than showing raw state

## Common Use Cases

**Running Example**: The following examples use a distributed termination detection specification with:
- `CONSTANT N` - Number of nodes
- `Node` - The set of nodes (e.g., `1..N` or `{n1, n2, n3}`)
- `VARIABLE active` - Function from nodes to booleans (whether each node is active)
- `VARIABLE counter` - Function from nodes to integers (message counter per node)
- `VARIABLE network` - Sequence of in-flight messages
- `VARIABLE color` - Function from nodes to colors (for termination detection)
- `VARIABLE terminated` - Boolean indicating whether termination has been detected
- `VARIABLE msgId`, `VARIABLE debugInfo` - Additional implementation detail variables that we may want to hide in traces

### 1. Filter Out Implementation Variables

Hide internal bookkeeping variables and show only the important state:

```tla
\* Full state includes: active, counter, network, color, terminated, msgId, debugInfo
Alias == [
    active |-> active,
    counter |-> counter,
    network |-> network,
    terminated |-> terminated
    \* msgId and debugInfo are hidden
]
```

### 2. Rename Variables for Clarity

Give variables more descriptive names in the trace output:

```tla
Alias == [
    nodesActive |-> active,
    msgCounters |-> counter,
    messagesInFlight |-> network,
    terminationDetected |-> terminated
]
```

### 3. Add Computed Properties

Display derived values alongside state variables:

```tla
Alias == [
    \* State variables
    active |-> active,
    counter |-> counter,
    network |-> network,
    \* Computed properties
    totalMessages |-> Len(network),
    activeCount |-> Cardinality({n \in Node : active[n]}),
    allInactive |-> \A n \in Node : ~active[n],
    messagesPending |-> Len(network) > 0,
    totalCounter |-> LET sum[i \in 0..N] == 
                         IF i = 0 THEN 0 ELSE sum[i-1] + counter[i]
                     IN sum[N]
]
```

### 4. Filter and Pretty Print Complex Values

Filter out empty or default values and format complex structures for readability:

```tla
Alias == [
    \* Only show active nodes
    activeNodes |-> {n \in Node : active[n]},
    \* Only show non-zero counters
    nonZeroCounters |-> [n \in {i \in Node : counter[i] # 0} |-> counter[n]],
    \* Format network messages for readability
    messages |-> [i \in 1..Len(network) |-> 
                    [from |-> network[i].sender,
                     to |-> network[i].receiver,
                     val |-> network[i].value]]
]
```

### 5. Include Trace Metadata for Debugging

Use `TLCGet` to include trace position and other metadata:

```tla
Alias == [
    \* Trace position
    step |-> TLCGet("level"),
    statesExplored |-> TLCGet("distinct"),
    \* State
    active |-> active,
    counter |-> counter,
    network |-> network
]
```

### 6. Use ENABLED to Diagnose Liveness Violations

When TLC reports a liveness violation, understanding which actions are enabled (or disabled) at each step is crucial for diagnosing why progress isn't being made:

```tla
Alias == [
    \* State variables
    active |-> active,
    counter |-> counter,
    network |-> network,
    terminated |-> terminated,
    \* Show which actions are enabled per node
    enabled |-> [
        SendMsg |-> [n \in Node |-> ENABLED SendMsg(n)],
        RecvMsg |-> [n \in Node |-> ENABLED RecvMsg(n)],
        Deactivate |-> [n \in Node |-> ENABLED Deactivate(n)],
        DetectTermination |-> ENABLED DetectTermination
    ]
]
```

This helps answer questions like:
- Why isn't the desired action ever taken?
- Are fairness conditions being violated?
- Is the system stuck in a cycle where certain actions are never enabled?

### 7. Include Constants for Context

Sometimes it's helpful to include constant values in the trace to provide context:

```tla
Alias == [
    \* Constants
    NodeCount |-> N,
    \* State variables
    active |-> active,
    counter |-> counter,
    network |-> network,
    \* Derived from constants
    maxMessages |-> N * (N - 1)
]
```

### 8. Create Node-Local Perspectives

While TLA+ uses global state (making reasoning about systems easy), analyzing traces can become easier when viewing the system from node-local perspectives that show what state is visible or accessible to each actor. Use functions as data structures to map each node to its local view:

```tla
LocalView(n) == [
    \* What this node directly controls
    myState |-> [
        active |-> active[n],
        counter |-> counter[n],
        color |-> color[n]
    ],
    \* What this node can observe
    observable |-> [
        inbox |-> SelectSeq(network, LAMBDA msg: msg.receiver = n),
        outbox |-> SelectSeq(network, LAMBDA msg: msg.sender = n),
        sentMsgCount |-> Len(SelectSeq(network, LAMBDA msg: msg.sender = n))
    ]
]

Alias == [
    \* Function mapping each node to its local perspective
    nodeViews |-> [n \in Node |-> LocalView(n)],
    \* Only show nodes with pending messages
    activeInboxes |-> {n \in Node : 
        Len(SelectSeq(network, LAMBDA msg: msg.receiver = n)) > 0},
    \* Global state for context
    totalMessages |-> Len(network),
    terminated |-> terminated
]
```

This approach is particularly useful for:
- Understanding distributed algorithms by seeing what each node can observe
- Debugging message-passing protocols by tracking per-node message queues
- Analyzing actor-based systems where each actor has local state
- Identifying information asymmetries between nodes
- Using functions as data structures to organize complex state hierarchically

### 9. Compose ALIAS Expressions

You can compose multiple ALIAS records using the record extension operator `@@`:

```tla
BaseAlias == [
    active |-> active,
    counter |-> counter,
    network |-> network
]

ComputedAlias == [
    activeCount |-> Cardinality({n \in Node : active[n]}),
    messageCount |-> Len(network)
]

DebugAlias == [
    level |-> TLCGet("level"),
    terminated |-> terminated
]

\* Combine them
FullAlias == BaseAlias @@ ComputedAlias @@ DebugAlias
```

This is useful when you have:
- A common base alias used across multiple specifications
- Separate debug information you want to optionally include
- Different views for different debugging scenarios

### 10. Load Modules Locally for Formatting

You can use `INSTANCE` within a `LET` expression to load modules locally and use their operators for formatting:

```tla
Alias == [
    active |-> active,
    network |-> network,
    \* Format the network as JSON for external tools
    _networkJson |->
        LET J == INSTANCE Json
        IN J!ToJson(network),
    \* Format entire state as JSON
    _stateJson |->
        LET J == INSTANCE Json
        IN J!ToJson([
            active |-> active,
            counter |-> counter,
            network |-> network
        ])
]
```

**Benefits**:
- Clean separation between specification logic and trace formatting
- No need to modify main module imports
- Can use different modules for different formatting needs within the same ALIAS

### 11. View High-Level Spec Variables When Checking Refinement

> **See also**: For a comprehensive guide on TLA+ refinement concepts, how to check refinement with TLC, and detailed examples, see [TLA+ Spec Refinement](tla-refinement.md).

When checking that a low-level specification refines a high-level specification under a refinement mapping, you may wish to see the values of the variables from the high-level specification alongside the low-level implementation variables. While you cannot directly access the high-level spec's variables, you can add elements to the ALIAS that show the derived values computed by the refinement mapping.

This is particularly useful when:
- Verifying refinement correctness without rewriting invariants for the low-level spec
- Understanding how low-level implementation maps to high-level abstraction
- Debugging refinement mapping errors by comparing both views side-by-side

**Example**: Suppose we have a low-level specification `TerminationDetectionIDs` that uses node identifiers, and it refines a high-level specification `TerminationDetectionNat` where nodes are modeled as naturals `0..N-1`. We want TLC to check refinement while viewing both the low-level and derived high-level values:

```tla
\* Define refinement mapping using INSTANCE
TerminationDetectionNat == 
    INSTANCE TerminationDetectionNat 
        WITH active <- NodeId2Nat(active),
             color <- NodeId2Nat(color),
             counter <- NodeId2Nat(counter),
             network <- NodeId2Nat(network)

\* ALIAS shows both low-level and high-level views
Alias == [
    \* Low-level implementation variables (using node identifiers)
    active |-> active,
    color |-> color,
    counter |-> counter,
    network |-> network,
    nodeIds |-> nodeIds,
    \* High-level abstraction variables (derived via refinement mapping)
    HL_active |-> NodeId2Nat(active),
    HL_color |-> NodeId2Nat(color),
    HL_counter |-> NodeId2Nat(counter),
    HL_network |-> NodeId2Nat(network)
]
```

**Result**: When TLC finds a counterexample (either to refinement or to an invariant), the trace displays both:
- The low-level implementation state (e.g., `active` using node identifiers)
- The corresponding high-level abstract state (e.g., `HL_active` using naturals)

This makes it easy to:
- Verify that the refinement mapping is computing expected values
- Understand how implementation decisions map to abstract concepts
- Debug refinement violations by seeing both views simultaneously
- Avoid rewriting complex invariants for different node representations

**Note**: Prefix high-level variables with a distinctive marker (like `HL_`) to clearly distinguish them from low-level variables in traces.

### 12. Decompose Invariants for Violation Analysis

When an invariant violation occurs, it's often useful to understand which part of the invariant is false. ALIAS can help by evaluating each component separately.

If an invariant consists of multiple conjuncts and it's not clear which are false, the ALIAS can decompose the invariant into its constituent parts. For quantified invariants, ALIAS can also evaluate the condition for each value to identify which specific values violate the condition:

```tla
\* Suppose the invariant is:
Inv == /\ \A n \in Node : counter[n] >= 0 
       /\ Len(network) < 100
       /\ terminated => (\A n \in Node : ~active[n])

\* ALIAS decomposes the invariant and drills into quantified conjuncts
Alias == [
    active |-> active,
    counter |-> counter,
    network |-> network,
    terminated |-> terminated,
    \* Evaluate each conjunct separately
    I1 |-> \A n \in Node : counter[n] >= 0,
    I2 |-> Len(network) < 100,
    I3 |-> terminated => (\A n \in Node : ~active[n]),
    \* Drill down: evaluate quantified conditions per node
    I1_perNode |-> [n \in Node |-> counter[n] >= 0],
    I3_perNode |-> [n \in Node |-> terminated => ~active[n]]
]
```

When TLC finds an invariant violation, the trace will show:
- Which specific conjuncts (`I1`, `I2`, `I3`) are `TRUE` or `FALSE`
- For quantified conjuncts, which specific nodes satisfy the condition (map of `node |-> TRUE/FALSE`)

## Special Considerations

### Stuttering Steps

On stuttering steps (where no variables change), the ALIAS expression evaluates with `s = t`. This means:
- `x' = x` for all variables
- `x' - x = 0` for numeric variables
- Transition-based computations may show no change

Example from stuttering traces:

```
State 1: <Initial predicate>
/\ active = [n \in Node |-> FALSE]
/\ network = <<>>
/\ messageCount = 0
/\ allInactive = TRUE

State 2: Stuttering
```

### Temporal Properties and Liveness

ALIAS expressions work with all TLC modes:
- Invariant violations
- Liveness violations (temporal properties)
- Simulation mode traces

For liveness violations, the ALIAS helps understand cycles:

```tla
LivenessAlias == [
    active |-> active,
    network |-> network,
    backToStart |-> network' = <<>>,
    cycleDetected |-> TLCGet("level") > 5 /\ network' = <<>>
]
```

### Initial State Handling

For the **initial state** (State 1 in traces), there is no previous state. TLC evaluates the ALIAS for the initial state as if `s = t`, which has the same observable effect as a stuttering step.

## Practical Workflow

### 1. Run TLC Without ALIAS

First, run TLC to find a counterexample and examine the raw trace output.

### 2. Analyze Raw Trace

Examine the error trace to understand what happened. Identify:
- Which variables are most relevant to understanding the bug
- What derived values would provide insight
- Whether any variables contain too much detail
- Whether constants would provide helpful context

### 3. Design ALIAS Expression

Create an ALIAS that highlights the important aspects:

```tla
Alias == [
    \* Filter to key variables
    active |-> active,
    network |-> network,
    \* Add derived values for insight
    activeCount |-> Cardinality({n \in Node : active[n]}),
    messageCount |-> Len(network),
    allInactive |-> \A n \in Node : ~active[n]
]
```

### 4. Rerun with ALIAS

Update your `.cfg` file and rerun TLC:

```
ALIAS Alias
```

If you already have the trace saved, you can use trace loading to replay it with the new ALIAS without re-exploring the state space.

### 5. Iterate

Refine your ALIAS based on what you learn. Common iterations:
- Add more derived values
- Filter out empty collections or default values
- Add pretty-printing for complex structures
- Include trace metadata for debugging
- Group related fields together

## Advanced: Using ALIAS with Trace Loading

The ALIAS feature is especially powerful when combined with TLC's trace loading capability.

### Workflow

1. **Generate trace**: Run TLC which finds a counterexample and automatically saves a trace file

2. **Refine ALIAS**: Update your specification to add/modify ALIAS expressions

3. **Replay trace**: Load the trace file to see the same counterexample with your new ALIAS visualization

This allows you to:
- Experiment with different ALIAS expressions without re-exploring the state space
- Add debugging information after finding a bug
- Share trace files with customized views for different audiences
- Debug trace acceptance in trace validation specifications

## Limitations

### 1. Single ALIAS per Configuration

You can only specify one ALIAS operator name in a `.cfg` file. However, you can combine multiple alias expressions using TLA+'s record merge operator `@@`:

```tla
\* Define component aliases
BaseAlias == [
    active |-> active,
    counter |-> counter,
    network |-> network
]

DebugAlias == [
    level |-> TLCGet("level"),
    terminated |-> terminated
]

\* Combine them with @@
CombinedAlias == BaseAlias @@ DebugAlias
```

```
ALIAS CombinedAlias
```

### 2. Action-Level Only

ALIAS expressions are action-level (Level 2). You cannot:
- Use temporal operators (`[]`, `<>`, `~>`)
- Reference multiple steps back in history (workaround below)
- Accumulate information across states

### 3. Record Structure Expected

If the ALIAS expression does not evaluate to a record, TLC will ignore the ALIAS and display the full state.

## Summary

ALIAS is a powerful feature for customizing trace output in TLC:

- **Define once, use everywhere**: Add `ALIAS AliasName` to your `.cfg` file and define the operator in your `.tla` file
- **Action-level evaluation**: Can reference both current (`x`) and next (`x'`) state values
- **Record-valued**: Must return a record where fields become displayed variables
- **Non-invasive**: Doesn't affect model checking results, only display
- **Composable**: Use `@@` to combine multiple ALIAS records
- **Tool-friendly**: Can format output for external tools (ShiViz, custom analyzers)
- **Debugging aid**: Essential for trace validation and understanding complex counterexamples
