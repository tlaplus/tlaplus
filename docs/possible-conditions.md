# Possibility Conditions with TLC's `_POSSIBLE`

## Why check that something *can* happen

When TLC reports that all invariants and properties hold, the result may be misleading if the model omits intended behaviors. A specification that permits only stuttering steps, an action whose enabling condition is too strong, or a model whose constant assignments are too small can cause TLC to explore too little while reporting no error. Always be suspicious of success.

The traditional remedy is to add `INVARIANT ~P` temporarily and check that it *fails*, which proves that a state satisfying `P` is reachable. Doing this by hand is tedious, easy to forget, and impossible to keep in the configuration file, since it makes a passing run fail. `_POSSIBLE` lets you keep the check in the configuration file:

```tla
SPECIFICATION Spec
INVARIANT TypeOK
_POSSIBLE
    LeaderElected
    BufferFull
    ReconfigurationCommitted
```

Each listed definition is a possibility condition, which TLC's messages call a `_POSSIBLE` predicate: a zero-arity state predicate or action; constant and temporal formulas are rejected. A state predicate is witnessed by a state satisfying it, an action by a step satisfying it. TLC fails the run unless every listed condition has a witness.

## An unwitnessed possibility condition

If TLC sent you here, it printed a record of witness counts followed by an error:

```
[BufferFull |-> 217, LeaderElected |-> 0]
Error: The _POSSIBLE predicate LeaderElected at line 42, col 21 to line 42, col 38 of module MySpec was never witnessed.
Others may be unwitnessed too; only witnessed predicates appear with a
non-zero count in the record printed above.
See https://explain.tlapl.us/possible-conditions for additional details.
```

Here no state satisfies `LeaderElected`, or no step does if it is an action. TLC names one unwitnessed condition and stops there; which one is unspecified. Any number of the others can be unwitnessed too, and only the record identifies them all.

`_POSSIBLE` is provisional (hence the leading underscore) and may be renamed or removed in a future release.

## Witness counts

TLC counts witnesses rather than recording a Boolean value. The `_Possible` module exposes the counts as `_Counts`, a record mapping the name of each condition TLC evaluated to the number of evaluations that yielded TRUE, summed over all workers. A `POSTCONDITION` can therefore assert exact counts:

```tla
EXTENDS _Possible

\* Guarded: applying _Counts outside its domain is an error, not FALSE.
Count(name) == IF name \in DOMAIN _Counts THEN _Counts[name] ELSE 0

CountsPostCondition ==
    /\ Count("BufferFull") > 0
    /\ Count("ReconfigurationCommitted") = 42
```

Interpret the counts only in terms of TLC's exploration. A count records how many evaluations yielded TRUE, so it depends on which states and steps the exploration strategy visits: the reachable state graph in model-checking mode, the sampled behaviors in simulation mode. A condition's share of the counts does not estimate the probability that the corresponding state or step occurs in the real system; that would require a sampling distribution validated against the system, which TLC does not provide in the general case.

On a long run, watching the counts grow tells you far more about progress than the distinct-state count does. The `_Possible` module defines `_PrintCounts` for that purpose; use it with `_PERIODIC`, and TLC prints the counts every time it reports progress:

```tla
_PERIODIC _PrintCounts
```

## Limitations

- `_POSSIBLE` asserts that **some** reachable state or step is a witness. It does not assert that every behavior, or every behavior starting from a given state, contains one.
- A state or step excluded by a `CONSTRAINT` or `ACTION_CONSTRAINT` lies outside the model and so never witnesses a condition. A condition can be reported as unwitnessed although an excluded state or step satisfies it.
- The record of witness counts lists only the conditions TLC evaluated, so read a missing name as a zero count. A state predicate goes unevaluated when TLC evaluates no state, an action when it evaluates no step, as when a `CONSTRAINT` excludes every state. The error names it regardless, taking the name from the `_POSSIBLE` list rather than from the record.
- An unwitnessed condition fails the run before a `POSTCONDITION` is evaluated, so one reading `_Counts` runs only when every condition is witnessed.
- In simulation mode, an unwitnessed condition may only mean that the sampled behaviors missed it. Treat simulation counts as evidence, not proof.
- Possibility conditions are not preserved by refinement. A refinement need not exhibit every behavior of the specification it refines.
- Possibility conditions are not liveness properties. They say that a situation *can* occur, not that it *must*.

## How to use possibility conditions

**To justify a reduced model.** Every state-space reduction (smaller constants, a `CONSTRAINT`, a `VIEW`, or a coarser abstraction) trades coverage for tractability, and each one risks producing a model that verifies quickly because it no longer does anything interesting. Write down the situations that make the model worth checking before you start reducing it, encode them as possibility conditions, and then shrink the configuration. If a witness stops being reached, the reduction went too far, and you find out mechanically instead of by intuition.

**As regression tests on the specification.** Because an unwitnessed condition fails the run, a checked-in set of them catches a later edit that leaves an action never enabled or strengthens its enabling condition, instead of letting it silently shrink the set of behaviors.
