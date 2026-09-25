---
title: TLA+ Trace Validation Manual for Simple Systems
description: Complete guide to validating implementation traces against TLA+ specifications using NDJSON format. Learn to bridge the gap between formal models and running code by checking that system traces represent valid behaviors of your specifications.
---
# TLA⁺ Trace Validation Manual for Simple Systems (JSON Format)

## Table of Contents
1. [Introduction](#introduction)
2. [Overview of Trace Validation](#overview)
3. [Components](#components)
   - 3.1 Implementation Trace
   - 3.2 High-Level Specification
   - 3.3 Validation Specification
   - 3.4 Configuration File
4. [The Implementation Trace (NDJSON Format)](#implementation-trace)
5. [The High-Level Specification](#high-level-specification)
6. [The Validation Specification](#validation-specification)
7. [Event Interpretation and Mapping](#event-interpretation)
8. [Best Practices](#best-practices)
9. [Further Reading](#further-reading)

---

## 1. Introduction {#introduction}

This manual covers TLA⁺ trace validation for **systems with totally-ordered event traces**, where events are logged in newline-delimited JSON (NDJSON) format from a single point of observation.

**Key Benefits:**
- Validate that implementations match their specifications
- Catch subtle bugs in state transitions
- Gain confidence in implementation correctness
- Bridge the gap between formal models and running code

**The Core Idea:** Given a trace from a running system (a log of events in NDJSON format) and a TLA⁺ specification, trace validation checks whether the trace represents a valid behavior of the specification.

**Critical Requirement:** The specification's CONSTANT values (such as buffer sizes, thread counts, maximum values) **must be configured to match the implementation**. The trace was generated using specific parameter values, and validation will only succeed if the specification uses those same values.

**When to Use This Approach:**
- Single-threaded systems, state machines, or sequential event logs
- Systems with a global observer or deterministic behavior
- **Concurrent systems** where tracing is done at consistent phases (e.g., in critical sections or when holding a global lock)

**When NOT to Use:** Distributed systems without global synchronization or concurrent systems with arbitrary interleaving require advanced techniques like vector clocks or happens-before relations.

---

## 2. Overview of Trace Validation {#overview}

### The Validation Process

```
┌─────────────────────┐
│  Implementation     │
│  (Running System)   │
└──────────┬──────────┘
           │ produces
           ▼
┌─────────────────────┐
│ Implementation      │
│ Trace (NDJSON)      │  ◄── Input 1
└──────────┬──────────┘
           │
           │ mapped to
           ▼
┌─────────────────────┐     ┌─────────────────────┐
│ Validation          │────▶│ High-Level          │
│ Specification       │  ⊆  │ Specification       │  ◄── Input 2
│ (HourClockTrace)    │     │ (e.g., HourClock)   │
└──────────┬──────────┘     └─────────────────────┘
           │
           │ verified by
           ▼
┌─────────────────────┐
│ TLC Model Checker   │
└──────────┬──────────┘
           │
           ▼
    ✓ Trace Accepted
    ✗ Trace Rejected (Bug Found)
```

### Key Insight

The validation specification:
1. Reads the implementation trace sequentially
2. Constrains the specification to only behaviors matching the trace
3. Checks if such a behavior exists


---

## 3. Components {#components}

A complete trace validation setup requires three components:

### 3.1 Implementation Trace (e.g., `trace.ndjson`)
- A log file from the running system
- NDJSON format: one JSON object per line
- Contains sequential events
- Each line represents one observable event

### 3.2 High-Level Specification (e.g., `HourClock.tla`)
- The original TLA⁺ specification
- Defines abstract behavior
- Contains actions like `Tick`, `Reset`, etc.
- Models the system at a high level

### 3.3 Validation Specification (e.g., `HourClockTrace.tla`)
- A specialized TLA⁺ module that:
  - Reads and parses the NDJSON trace
  - Maps trace events to high-level actions
  - Constrains state space to match the trace
  - Defines acceptance criteria

### 3.4 Configuration File (e.g., `HourClockTrace.cfg`)
- Assigns values to CONSTANTS
- Specifies the VIEW
- Sets model-checking parameters
- **Critical:** CONSTANT values must match the implementation's configuration

---

## 4. The Implementation Trace {#implementation-trace}

### 4.1 NDJSON Structure

An NDJSON trace is a text file where each line is a valid JSON object representing an event. NDJSON (Newline Delimited JSON) is a format where:
- Each line is a separate, self-contained JSON value
- Lines are separated by newline characters (`\n`)
- Each JSON object is independent and can be parsed individually

**Example: Hour Clock Trace**

```json
{"event": "init", "hour": 1}
{"event": "tick", "hour": 2}
{"event": "tick", "hour": 3}
{"event": "tick", "hour": 4}
{"event": "tick", "hour": 5}
{"event": "tick", "hour": 6}
{"event": "tick", "hour": 7}
{"event": "tick", "hour": 8}
{"event": "tick", "hour": 9}
{"event": "tick", "hour": 10}
{"event": "tick", "hour": 11}
{"event": "tick", "hour": 12}
{"event": "tick", "hour": 1}
{"event": "tick", "hour": 2}
```

### 4.2 Design Principles

**Why NDJSON?**
- **Streamable:** Each event can be processed independently
- **Human-readable:** Easy to inspect and debug
- **Machine-friendly:** Simple to parse in any language
- **Structured:** JSON provides data types (numbers, booleans, nested objects, arrays)
- **Self-documenting:** Field names are explicit in each record
- **Flexible:** Easy to add new fields without breaking parsers

**Line-based Processing:**
Each line is a complete JSON object, making it easy to:
- Append new events as they occur
- Read large traces incrementally
- Recover from partial corruption (bad lines can be skipped)

### 4.3 JSON Data Types in Traces

JSON supports data types that map naturally to TLA⁺ values:

| JSON Type | Example | TLA⁺ Type | Notes |
|-----------|---------|-----------|-------|
| **Number** | `42`, `3.14` | Integer, Real | Parsed directly as numbers |
| **String** | `"tick"`, `"active"` | String | Use for event types, states |
| **Boolean** | `true`, `false` | BOOLEAN | Maps to TLA⁺ TRUE/FALSE |
| **Array** | `[1, 2, 3]` | Sequence | Maps to TLA⁺ sequences |
| **Object** | `{"x": 1, "y": 2}` | Record | Maps to TLA⁺ records |
| **Null** | `null` | - | Can represent absence of value |

### 4.4 Reading NDJSON in TLA⁺

TLA⁺ provides the `Json` module for reading JSON files. The `ndJsonDeserialize` operator reads NDJSON files:

```tla
EXTENDS Json

TraceLog == ndJsonDeserialize("trace.ndjson")
```

This produces a sequence of TLA⁺ values:
```tla
<< 
    [event |-> "tick", hour |-> 2],
    [event |-> "tick", hour |-> 3],
    [event |-> "tick", hour |-> 4],
    ...
>>
```

### 4.5 Logging Strategy

**When to Log:**

Log at **stable states** - points where the system is in a consistent, observable state:

```c
// Bad: Log before state update
printf("{\"event\": \"tick\", \"hour\": %d}\n", hour);
hour = (hour % 12) + 1;

// Better: Log after state update
hour = (hour % 12) + 1;
printf("{\"event\": \"tick\", \"hour\": %d}\n", hour);

// Best: Include before and after state
int old_hour = hour;
hour = (hour % 12) + 1;
printf("{\"event\": \"tick\", \"old_hour\": %d, \"hour\": %d}\n", 
       old_hour, hour);
```

Log **state snapshots** to include all relevant state:

```c
// Minimal
printf("{\"event\": \"tick\"}\n");

// Better: Include state
printf("{\"event\": \"tick\", \"hour\": %d}\n", hour);

// Best: Include all relevant state
printf("{\"event\": \"tick\", \"hour\": %d, "
       "\"alarm_set\": %s, \"alarm_hour\": %d}\n",
       hour,
       alarm_set ? "true" : "false",
       alarm_hour);
```

**What to Log:**

Log enough information to:
1. Identify which action occurred
2. Verify the new state is correct
3. Debug failures when validation fails

**Minimal Logging:**
```json
{"event": "tick"}
{"event": "tick"}
{"event": "tick"}
```
Problem: Can't verify state correctness!

**Better Logging:**
```json
{"event": "tick", "hour": 2}
{"event": "tick", "hour": 3}
{"event": "tick", "hour": 4}
```
Now we can verify that `hr` has the expected value.

---

## 5. The High-Level Specification {#high-level-specification}

The validation specification extends your existing high-level TLA⁺ specification. For example, a simple hour clock:

**File: `HourClock.tla`**

```tla
--------------------------- MODULE HourClock ---------------------------
EXTENDS Naturals

CONSTANT MaxHour

VARIABLE hr

HCini == hr \in 1..MaxHour

HCnxt == hr' = IF hr # MaxHour THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr
=============================================================================
```

**Key Point:** The `MaxHour` constant allows the specification to be parameterized. The actual value is set in the configuration file to match the implementation.

**File: `HourClock.cfg`**

```
CONSTANT MaxHour = 12
```

**Important:** When validating traces, the constant values in your configuration file **must match** the values used by your implementation. If your implementation uses a 24-hour clock, set `MaxHour = 24`. Mismatched constants are a common source of validation failures.

---

## 6. The Validation Specification {#validation-specification}

The validation specification is the **bridge** between the trace and the high-level spec.

### 6.1 Structure Overview

```tla
--------------------------- MODULE HourClockTrace --------------------------
EXTENDS HourClock, Json, TLC, Naturals

\* 1. Load the trace
Trace == ndJsonDeserialize("trace.ndjson")

\* 2. Define initialization
Init == hr = 1  \* More specific than HCini

\* 3. Define next-state: match trace event to spec action
Next == 
    LET level == TLCGet("level") IN
    /\ level <= Len(Trace)
    /\ Trace[level].event = "tick"
    /\ Trace[level].old_hour = hr
    /\ HCnxt
    /\ Trace[level].hour = hr'

\* 4. Complete specification
Spec == Init /\ [][Next]_hr

\* 5. Acceptance criterion
TraceAccepted ==
    LET d == TLCGet("stats").diameter IN
    IF d - 1 = Len(Trace) 
    THEN TRUE
    ELSE Print(<<"Failed at line:", Trace[d]>>, FALSE)

\* 6. View (MANDATORY when using TLCGet("level"))
TraceView == <<hr, TLCGet("level")>>

=============================================================================
```

**File: `HourClockTrace.cfg`**

```
CONSTANT MaxHour = 12

SPECIFICATION Spec
POSTCONDITION TraceAccepted
VIEW TraceView
```

**Critical Configuration Notes:**
- The `MaxHour` constant must match your implementation (e.g., if implementing a 24-hour clock, use `MaxHour = 24`)
- The `VIEW` directive is mandatory when using `TLCGet("level")`
- The `POSTCONDITION` checks that the entire trace is successfully validated

### 6.2 Key Components in Detail

#### 6.2.1 Loading the Trace

```tla
Trace == ndJsonDeserialize("trace.ndjson")
```

**Purpose:**
- Read the NDJSON file
- Parse each line as a JSON object
- Return a sequence of TLA⁺ records
- Make available to the rest of the spec

**File Path:** Can be:
- Relative to working directory: `"trace.ndjson"`
- Absolute path: `"/home/user/traces/trace.ndjson"`

**Example with environment variable:**
```tla
EXTENDS Json

Trace == 
    ndJsonDeserialize(
        IF "TRACE_FILE" \in DOMAIN IOEnv 
        THEN IOEnv.TRACE_FILE 
        ELSE "trace.ndjson"
    )
```

Then run:
```bash
TRACE_FILE=mytrace.ndjson tlc HourClockTrace.tla
```

#### 6.2.2 Initialization

```tla
Init == hr = 1
```

**Key Point:** Make initialization more specific than the high-level spec to match the actual implementation's initial state.

**Inferring from trace:**

If the first event logs the initial hour:
```json
{"event": "init", "hour": 7}
{"event": "tick", "hour": 8}
```

Then:
```tla
Init == hr = Trace[1].hour  \* Start at logged value (already an integer!)
```

#### 6.2.3 Next-State Action

```tla
Next == 
    LET level == TLCGet("level") IN
    /\ level <= Len(Trace)
    /\ Trace[level].event = "tick"
    /\ Trace[level].old_hour = hr
    /\ HCnxt
    /\ Trace[level].hour = hr'
```

**The Critical Pattern:**
- Event type check: `Trace[level].event = "tick"`
- Current state verification: `Trace[level].old_hour = hr`
- High-level action: `HCnxt`
- Next state verification: `Trace[level].hour = hr'`

This triple conjunction ensures the trace event matches both the expected action and resulting state.

**Using `TLCGet("level")`:**
- Returns the current step number in the behavior (starting at 1)
- Eliminates the need for an explicit index variable
- **Requires a VIEW** including `TLCGet("level")` to distinguish states (see section 6.2.6)

#### 6.2.4 Acceptance Criterion

```tla
TraceAccepted ==
    LET d == TLCGet("stats").diameter IN
    IF d - 1 = Len(Trace) 
    THEN TRUE
    ELSE Print(<<"Failed at line:", Trace[d]>>, FALSE)
```

**Purpose:** Verify the entire trace was successfully matched.

**Note:** Use `d - 1` because diameter counts states (including initial state) while `Len(Trace)` counts events.

#### 6.2.5 The View (Mandatory)

```tla
TraceView == <<hr, TLCGet("level")>>
```

**Purpose:** Prevent TLC from stopping when it encounters repeated states.

**Why mandatory when using `TLCGet("level")`:**

When using `TLCGet("level")` instead of an explicit index variable, the spec variables may not change between steps. For example:
- Step 10: `hr = 5`
- Step 11: `hr = 5` (another event at the same hour)

Without a view, TLC sees the same state (`hr = 5`) twice and stops exploration, thinking it has found a cycle. By including `TLCGet("level")` in the view, each step is considered distinct:
- Step 10: `<<5, 10>>`
- Step 11: `<<5, 11>>`

**Configuration:** Add to your `.cfg` file:
```
VIEW TraceView
```

**Important:** The view must include `TLCGet("level")` to ensure TLC processes the entire trace, even when consecutive trace events don't change the spec variables.

### 6.3 Alternative Patterns

#### Pattern 1: Multiple Event Types

If your system has different kinds of events:

```tla
Next == 
    LET level == TLCGet("level") IN
    /\ level <= Len(Trace)
    /\ CASE Trace[level].event = "tick"  -> 
                /\ HCnxt
                /\ Trace[level].hour = hr'
         [] Trace[level].event = "reset" -> 
                /\ Reset
                /\ Trace[level].hour = hr'
         [] OTHER -> FALSE  \* Unknown event type
```

#### Pattern 2: Partial Information

If the trace doesn't log all state:

```tla
Next == 
    LET level == TLCGet("level") IN
    /\ level <= Len(Trace)
    /\ Trace[level].event = "tick"
    /\ Trace[level].old_hour = hr
    /\ HCnxt
    \* No check of hr' - not logged
```

**Warning:** Less verification! Can't catch bugs in state computation.

#### Pattern 3: Non-Determinism

If the trace is incomplete and allows multiple possibilities:

```tla
Next == 
    LET level == TLCGet("level") IN
    /\ level <= Len(Trace)
    /\ Trace[level].event = "tick"
    /\ HCnxt
    /\ hr' \in {Trace[level].hour, Trace[level].hour + 1}
```

---

## 7. Event Interpretation and Mapping {#event-interpretation}

### 7.1 The Core Challenge

**Problem:** Map each trace event to a high-level specification action.

**Solution:** For each event type, define a predicate that:
1. Checks the event matches the expected pattern
2. Verifies the corresponding spec action occurred
3. Confirms the resulting state is correct

### 7.2 Example: Extended Hour Clock

Suppose we extend the hour clock with an alarm:

**High-Level Spec:**
```tla
EXTENDS Naturals

CONSTANT MaxHour

VARIABLES hr, alarm_set, alarm_hour
vars == <<hr, alarm_set, alarm_hour>>

TypeOK == 
    /\ hr \in 1..MaxHour
    /\ alarm_set \in BOOLEAN
    /\ alarm_hour \in 1..MaxHour

Init == 
    /\ hr \in 1..MaxHour
    /\ alarm_set = FALSE
    /\ alarm_hour \in 1..MaxHour

Tick ==
    /\ hr' = IF hr # MaxHour THEN hr + 1 ELSE 1
    /\ UNCHANGED <<alarm_set, alarm_hour>>

SetAlarm(h) ==
    /\ h \in 1..MaxHour
    /\ alarm_hour' = h
    /\ alarm_set' = TRUE
    /\ UNCHANGED hr

ClearAlarm ==
    /\ alarm_set' = FALSE
    /\ UNCHANGED <<hr, alarm_hour>>

Next ==
    \/ Tick
    \/ \E h \in 1..MaxHour : SetAlarm(h)
    \/ ClearAlarm
```

**Trace Format:**
```json
{"event": "tick", "hour": 2, "alarm_set": false, "alarm_hour": 12}
{"event": "tick", "hour": 3, "alarm_set": false, "alarm_hour": 12}
{"event": "set_alarm", "hour": 3, "alarm_set": true, "alarm_hour": 6}
{"event": "tick", "hour": 4, "alarm_set": true, "alarm_hour": 6}
{"event": "tick", "hour": 5, "alarm_set": true, "alarm_hour": 6}
{"event": "tick", "hour": 6, "alarm_set": true, "alarm_hour": 6}
{"event": "clear_alarm", "hour": 6, "alarm_set": false, "alarm_hour": 6}
{"event": "tick", "hour": 7, "alarm_set": false, "alarm_hour": 6}
```

**Note:** JSON booleans (`true`, `false`) map directly to TLA⁺ (`TRUE`, `FALSE`)!

**Validation Spec:**
```tla
EXTENDS AlarmClock, Json, TLC

TraceLog == ndJsonDeserialize("trace.ndjson")

Init == 
    /\ hr = 1
    /\ alarm_set = FALSE
    /\ alarm_hour = MaxHour  \* Use the constant

event ==
    LET level == TLCGet("level") IN
    /\ level <= Len(TraceLog)
    /\ LET event == TraceLog[level] IN

IsTick ==
    /\ event.event = "tick"
    /\ Tick
    /\ hr' = event.hour

IsSetAlarm ==
    /\ event.event = "set_alarm"
    /\ SetAlarm(event.alarm_hour)
    /\ hr' = event.hour
    /\ alarm_set' = event.alarm_set

IsClearAlarm ==
    /\ event.event = "clear_alarm"
    /\ ClearAlarm
    /\ hr' = event.hour
    /\ alarm_set' = ~event.alarm_set

Next ==
    \/ IsTick
    \/ IsSetAlarm
    \/ IsClearAlarm

Spec == Init /\ [][Next]_vars

TraceAccepted ==
    LET d == TLCGet("stats").diameter IN
    IF d - 1 = Len(Trace) 
    THEN TRUE
    ELSE Print(<<"Failed at line:", Trace[d]>>, FALSE)

\* Don't forget the mandatory VIEW!
TraceView == <<vars, TLCGet("level")>>
```

**Configuration file:**
```
CONSTANT MaxHour = 12

SPECIFICATION Spec
POSTCONDITION TraceAccepted
VIEW TraceView
```

### 7.3 Design Principles

**1. One Predicate Per Event Type**

Good:
```tla
IsTick(e) == e.event = "tick" /\ Tick /\ e.hour = hr'
IsSetAlarm(e) == e.event = "set_alarm" /\ SetAlarm(e.alarm_hour) /\ ...
```

Bad:
```tla
IsEvent(e) == Next  \* Too broad!
```

**2. Check Event Fields First**

Good ordering:
```tla
IsTick(e) ==
    /\ e.event = "tick"      \* Cheap check first
    /\ e.old_hour = hr       \* Current state verification
    /\ Tick                  \* Expensive action check
    /\ e.hour = hr'          \* Next state verification
```

**3. Verify State Consistency**

Always check that the logged state matches the computed state:
```tla
/\ e.hour = hr'              \* Direct integer comparison
/\ e.alarm_set = alarm_set'  \* Direct boolean comparison
```


---

## 8. Best Practices {#best-practices}

**1. Match CONSTANTS to Implementation**

Always set CONSTANT values in your configuration file to match your implementation:

```tla
\* Specification
CONSTANT MaxHour, MaxBufferSize, NumThreads

\* Configuration file
CONSTANT 
    MaxHour = 12
    MaxBufferSize = 100
    NumThreads = 4
```

**Why this matters:**
- Your implementation has concrete values for parameters
- The trace was generated with those specific values
- Mismatched constants will cause validation to fail
- Example: If implementation uses a 24-hour clock but spec uses `MaxHour = 12`, validation will reject traces with hour values 13-24

**2. Follow the Small Scope Hypothesis for Constants Not in Trace**

When your specification requires constant values that don't appear in the trace (e.g., data values stored in data structures), use the smallest possible set that enables validation:

```tla
\* If the system stores arbitrary data values in a queue
CONSTANT Data
```

**Good practice:**
```
\* Configuration file
CONSTANT Data = {1, 2, 3}  \* Minimal set for trace validation
```

**Why this matters:**
- Smaller constants reduce the state space, making model checking faster
- The trace only exercises specific values; other values are irrelevant for validation
- Following the small scope hypothesis aligns with effective model checking practice
- Example: If a queue trace shows enqueuing/dequeuing but never logs the actual data values, use a minimal set like `{d1, d2}` rather than a large range like `1..100`

**When to use minimal constants:**
- Data values that are opaque to the specification (e.g., queue contents where only structure matters)
- Thread/process IDs when the trace doesn't distinguish between them
- Enumeration types where the trace uses only a subset
- Any value that serves as a placeholder rather than affecting control flow

## 9. Further Reading {#further-reading}

- [Smart Casual Verification of the Confidential Consortium Framework](https://arxiv.org/abs/2406.17455)
- [Validating Traces of Distributed Programs Against TLA+ Specifications](https://arxiv.org/abs/2404.16075)
- [EWD998 Example Implementation](https://github.com/tlaplus/Examples/blob/master/specifications/ewd998/EWD998ChanTrace.tla)
- [Ron Pressler's Talk on Trace Validation](https://www.youtube.com/watch?v=TP3SY0EUV2A)
- [NDJSON Specification](http://ndjson.org/)
- [JSON.org - JSON Specification](https://www.json.org/)
- [TLA+ Json Module Documentation](https://github.com/tlaplus/CommunityModules/blob/master/modules/Json.tla)