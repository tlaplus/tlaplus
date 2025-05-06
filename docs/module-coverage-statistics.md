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
The line `<x line 4, col 11 to line 4, col 11 of module Foobar>:10` indicates that TLC found 10 distinct values for the (declared) variable `x`.

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

These costs can highlight performance hotspots in your specification—helpful for optimizing large models where memory usage or computational effort may become significant.