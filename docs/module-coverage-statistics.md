# Understanding TLC Module Coverage Statistics

When you run the TLC Model Checker with the -coverage 1 flag, TLC prints out coverage statistics every minute and once again at the end of model checking. You can adjust the interval (e.g., -coverage 5) if you want less frequent updates.

Consider the following simple specification:

```tla
------ MODULE Foobar ------
EXTENDS Naturals

VARIABLES x

Init ==
    /\ x = 0

Inc ==
    /\ x < 10
    /\ x >= 0
    /\ x' = x + 1

Dec ==
    /\ x < 10
    /\ x > 0
    /\ x' = x - 1

Next ==
    \/ Inc
    \/ Dec

Spec ==
    Init /\ [][Next]_x

=====
```

When TLC runs this spec with coverage reporting enabled (and without deadlock checking), it produces output like this:

```
The coverage statistics at 2025-04-02 18:02:30
<x line 4, col 11 to line 4, col 11 of module Foobar>: 10
<Init line 6, col 1 to line 6, col 4 of module Foobar>: 1:1
  line 7, col 5 to line 7, col 12 of module Foobar: 1
<Inc line 9, col 1 to line 9, col 3 of module Foobar>: 10:10
  line 10, col 8 to line 10, col 13 of module Foobar: 10
  |line 10, col 8 to line 10, col 8 of module Foobar: 11
  line 11, col 8 to line 11, col 13 of module Foobar: 10
  line 12, col 8 to line 12, col 17 of module Foobar: 10
<Dec line 14, col 1 to line 14, col 3 of module Foobar>: 0:9
  line 15, col 8 to line 15, col 13 of module Foobar: 9
  |line 15, col 8 to line 15, col 8 of module Foobar: 11
  line 16, col 8 to line 16, col 12 of module Foobar: 9
  |line 16, col 8 to line 16, col 8 of module Foobar: 10
  line 17, col 8 to line 17, col 17 of module Foobar: 9
End of statistics.
```

## How to Interpret This Output
Each block of coverage statistics corresponds to either a variable declaration, a definition (like `Init`, `Inc`, or `Dec`), or an expression inside the definition.

### Variable Declaration:
The line `<x line 4, col 11 to line 4, col 11 of module Foobar>: 10` indicates that TLC found 10 distinct values for the (declared) variable `x`.

### State-level expressions (`Init`):

The line `<Init line 6, col 1 to line 6, col 4 of module Foobar>: 1:1` shows that TLC evaluated the `Init` predicate once, and it produced one initial state. 

### Action-level expressions (`Inc` and `Dec`):

Lines like `<Inc line 9, col 1 to line 9, col 3 of module Foobar>: 10:10` indicate how many times TLC evaluated this action and how many of those evaluations led to new (unseen) states. `10:10` means `Inc` was evaluated 10 times, and each time resulted in a new state. `0:9` for `Dec` means `Dec` was evaluated 9 times, but none of those evaluations produced a new state.

### Sub-Expressions:

Lines such as `line 10, col 8 to line 10, col 13 of module Foobar: 10` report how many times each subexpression was evaluated. Lines starting with `|` (e.g., `|line 10, col 8 to line 10, col 8 of module Foobar: 11`) indicate coverage for sub-subexpressions, such as terms inside a larger expression. These are often evaluated more frequently because they're reused in different contexts or branches.

## Costs of expressions

In addition to tracking how many times an expression is evaluated, TLC also reports the computational cost of evaluating certain expressions—particularly those that require constructing or allocating internal data structures during successor state generation.

This is especially relevant for expressions that manipulate sets, functions, sequences, or other compound structures. When such an allocation occurs, TLC appends a second number to the coverage entry in the format evaluations:cost.

Consider the following specification, where the `Next` action repeatedly adds a new element to the set `x`:

```tla
------ MODULE Costs ------
EXTENDS Naturals, FiniteSets

VARIABLES x

Init ==
    x = {}

Next ==
    /\ Cardinality(x) < 10
    /\ x' = x \union {Cardinality(x) + 1}

Spec ==
    Init /\ [][Next]_x

=====
```

```
The coverage statistics at 2025-04-02 18:28:21
<x line 4, col 11 to line 4, col 11 of module Foobar>:10
Init line 6, col 1 to line 6, col 4 of module Foobar>: 1:1
  line 7, col 5 to line 7, col 10 of module Foobar: 1
<Next line 9, col 1 to line 9, col 4 of module Foobar>: 10:10
  line 10, col 8 to line 10, col 26 of module Foobar: 10
  |line 10, col 8 to line 10, col 21 of module Foobar: 11
  line 11, col 8 to line 11, col 41 of module Foobar: 10
  |line 11, col 13 to line 11, col 41 of module Foobar: 10
  ||line 11, col 13 to line 11, col 13 of module Foobar: 10
  ||line 11, col 22 to line 11, col 41 of module Foobar: 10:18
  |||line 11, col 23 to line 11, col 40 of module Foobar: 10
End of statistics.
```

This tells us:

The sub-expression `({Cardinality(x) + 1})` was evaluated 10 times, and TLC incurred an allocation cost of 18 across those 10 evaluations. This cost represents internal overhead, such as memory allocation or structural copying involved in creating the new set value.

These costs can highlight performance hotspots in your specification—helpful for optimizing large models where memory usage or computational effort may become significant. High costs typically come from `SUBSET S`, function sets `[A -> B]`, set comprehensions, `Cardinality`, and quantification over large sets. Cost measures the work per step rather than the number of states, but the two usually travel together, because the expression that enumerates a large set is often also the one that produces many successors.

## Using Coverage as a Diagnosis

Coverage is a profiling tool: it identifies expensive formulas and sources of state-space explosion. It is not structural or source coverage of the kind used with programming languages.

TLA+ is a state-based formalism. There is no program counter, and a formula is not a statement that executes. TLC records how often it evaluated a formula while generating and checking states. Statement, branch, or MC/DC coverage would be a different concept, not a more detailed form of this report.

### Reading variable coverage

The number of distinct values per variable is the most direct handle on the size of the state space, since the product of these numbers bounds it. Read the report looking for outliers.

A variable with significantly more values than the others is usually what drives state space explosion. The usual offenders are history variables and logs that only grow, unbounded counters, and message queues or sequences that accumulate duplicates. Ask whether anything in the invariants and properties actually observes the variable, whether a sequence can be replaced by a set or a counter, and whether a `CONSTRAINT` should bound it.

A variable with suspiciously *few* values deserves attention as well. A counter that never gets past 1 usually means the constants are too small or that some behavior is unreachable.

### Reading expression coverage

The indented lines beneath a definition report how often TLC evaluated each subexpression and, where the evaluation allocated, at what cost. Neither number is elapsed time; together they locate the subexpression that accounts for most of the work in that definition.

| Pattern                                                     | Reading                                                                                                                                                                                                                                             |
| ----------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Evaluated far more often than the expression containing it  | The expression sits inside an enumeration (`\E`, `\A`, a set comprehension, `CHOOSE`) and is re-evaluated per element. If it does not depend on the bound identifier, lift it out of the enumeration, into a `LET` above it or a separate definition. |
| Counts dropping from one conjunct to the next               | TLC evaluates a conjunct list in order and stops at the first `FALSE`, so the drop marks the selective conjunct. Put the cheapest and most selective conjuncts first, so that expensive ones are reached less often.                                 |
| Cost much larger than the number of evaluations             | The expression allocates on every evaluation. Enumerating `SUBSET S` or `[A -> B]` to pick one element is the usual case; construct the element directly instead, or shrink the set it ranges over.                                                  |

Before rewriting an expensive operator by hand, check whether the [CommunityModules](https://modules.tlapl.us) already define it. They collect operators that recur across specifications, and a number of them come with Java module overrides. An override is not merely a constant-factor speedup: where the TLA+ definition has to be written constructively and TLC therefore enumerates, the Java implementation can use an algorithm of lower complexity.

### Reading action coverage

Recall that next-state actions print `distinct:generated`.

| Pattern                                                     | Reading                                                                                                                                                                                                                                             |
| ----------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Large first number                                          | This action is a main source of distinct states; effort spent constraining it shrinks the state space.                                                                                                                                              |
| First number much smaller than the second (including `0:N`) | Most generated successors were already in the state space. That costs time, not memory, and it is expected of an action that mostly leads back to states other actions already reach. It is a correctness issue only if you expected the action to add distinct states. |
| Both numbers 0                                              | The action never produced a successor. Look at its subexpressions: non-zero counts mean TLC tried it and found it disabled; zeros throughout suggest it is unreachable or not a disjunct of the next-state relation.                                 |
| Many actions each with a large first number                 | A genuine interleaving explosion. Consider coarsening atomicity, that is, merging steps whose interleaving no invariant or property can observe.                                                                                                     |

A large number of initial states is easy to overlook, and it is a common reason for a state space that is already large before model checking begins. The first number of the `Init` entry reports that count (`Init` uses a related but not identical pair of counters to next-state actions).

### Coverage is not free

TLC collects coverage in a way that Java's just-in-time compiler can eliminate entirely when it is disabled, so enabling it costs real throughput. TLC says as much when it finishes:

```
End of statistics (please note that for performance reasons large models
are best checked with coverage and cost statistics disabled).
```

Use coverage on short diagnostic runs, and turn it off for the long production run.

Most of that overhead comes from counting every subexpression evaluation. If the numbers you are after are the per-action, per-init, and per-variable ones, there is a middle ground: the system property `-Dtlc2.TLCGlobals.coverage=N` maintains those counters alone, and leaves them to be read from within the specification rather than printed. See *Advantages and limitations of `TLCGet("spec").actions`* below.

## Coverage data in `TLCGet("spec")`

The coverage report above is written for a human reader, and its custom format takes some work to parse. Part of the same data is also available to the specification itself. `TLCGet("spec")` returns a record describing the elements of the specification TLC is checking, and when coverage collection is enabled, most of those elements carry an extra `coverage` field holding the counters TLC kept for them.

Evaluate it from a `POSTCONDITION`, where the counters have reached their final values. For the `Foobar` module above, with `TLC` added to its `EXTENDS`,

```tla
PostCondition ==
    PrintT(TLCGet("spec").actions)
```

together with `POSTCONDITION PostCondition` in the configuration file, prints

```tla
{ [ coverage |-> [generated |-> 9, distinct |-> 0],
    name |-> "Dec",
    location |->
        [ beginLine |-> 15,
          beginColumn |-> 5,
          endLine |-> 17,
          endColumn |-> 17,
          module |-> "Foobar" ] ],
  [ coverage |-> [generated |-> 10, distinct |-> 10],
    name |-> "Inc",
    location |->
        [ beginLine |-> 10,
          beginColumn |-> 5,
          endLine |-> 12,
          endColumn |-> 17,
          module |-> "Foobar" ] ] }
```

Besides `actions`, the record has the fields `inits`, `invariants`, `temporals`, `impliedinits`, `impliedactions`, `impliedtemporals`, `constraints`, `actionconstraints`, and `variables`. Each is a set of records carrying a `name` and a `location`, plus a `coverage` for the kinds TLC keeps counters for

### Advantages and limitations of `TLCGet("spec").actions`

The record exposes the header line of each block of the report, and only the header line:

| Field | `coverage` | What the counter is |
| ----- | ---------- | ------------------- |
| `inits`, `actions` | `generated`, `distinct` | The `distinct:generated` pair the header line prints |
| `invariants`, `impliedinits`, `impliedactions` | `count` | How often the body was evaluated, read off one of its subexpressions, chosen arbitrarily if there are several. The header line itself prints no number |
| `variables` | `distinct` | The number of distinct values of the declared variable |

What the record adds:

**Parameters of a sub-action.** `Step(self)` with `self \in {1, 2, 3}` yields one element per context, each with a `context` field (`[self |-> 1]`) and a `parameters` field (`<<"self">>`), where the report prints a single block for all three.

**Names for implied initial predicates and implied actions.** The report labels them with the generic `<Action ...>`; the records carry the name of the `PROPERTY` they come from.

**Counters without a report.** `-coverage N` fills in every field above, but also prints the report every `N` minutes. The system property `-Dtlc2.TLCGlobals.coverage=3` maintains the counters and prints nothing; bit 1 enables the action and init counters, bit 2 the variable ones. An invariant's `count` stays 0, since subexpression counters are maintained under `-coverage` alone. Note that `-coverage 0` does not suppress the report either: the value is an interval in minutes, and 0 makes TLC print at every progress interval.

Where the record falls short:

**No subexpression counts and no costs.** The indented lines have no counterpart, which rules out the diagnoses described above: an invariant that holds vacuously in every state and one that is evaluated in full report the same `count`. The `evaluations:cost` pair belongs to a subexpression and is not exposed either.

**No counters for constraints or temporal formulas.** Elements of `constraints` and `actionconstraints` carry `name` and `location` only, although the report does print a `distinct:generated` pair for each `CONSTRAINT` and `ACTION_CONSTRAINT`. Temporal formulas have no counters in either rendering, because liveness is not checked by evaluating a formula once per state.

**Counters are per definition, not per context.** All contexts of `Step(self)` share one cost model and report the same totals, so summing `coverage.generated` over `actions` counts each evaluation once per parameter value.

**Locations point at the body, not at the name.** The report prints `<Inc line 9, col 1 to line 9, col 3 of module Foobar>`, the location of the name; the record gives lines 10 to 12, the location of the body. The two renderings cannot be matched up by location.

**Counts above 2^31-1 come out as -1.** TLC's integers are 32 bit, and a count that does not fit is replaced silently rather than reported as an error. Counts of that size are ordinary on a model large enough to be worth profiling.

**In simulation mode, `distinct` is meaningless.** An action reports `distinct` equal to `generated`, a variable reports 0.

Finally, mind where you call `TLCGet("spec")`. In a `POSTCONDITION` the workers have finished and the numbers are final; in an invariant or a constraint it is a snapshot taken while the workers count, so the numbers race with evaluation and need not be consistent with one another.

### Serializing the data

Since this is an ordinary TLA+ value, any operator that accepts a value can consume it, and the format is the user's choice. `PrintT` above writes the value in TLA+ syntax, which is already machine-readable and can be pasted back into a specification. The `Json` module is one alternative among several: `Json!ToJson` converts a value to a JSON string, `Json!JsonSerialize` writes a tuple of values to a file as JSON, and `Json!ndJsonSerialize` writes newline-delimited JSON. Replacing the `PostCondition` above with

```tla
PostCondition ==
    JsonSerialize("coverage.json", <<TLCGet("spec")>>)
```

writes the whole record to `coverage.json`. Records become JSON objects, and sets and tuples become JSON arrays. Since `JsonSerialize` takes a tuple of values, the file holds an array whose single element is the record. The Community Modules add further serialization operators, and because the coverage data is a plain record you can also compute a format of your own in TLA+ before writing it out.
