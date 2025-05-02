# Replacing `Seq` with `BoundedSeq` for Finite-State Model Checking with TLC

```tla
----- MODULE Simple -----
EXTENDS Sequences

S == {"a", "b"}

VARIABLE log

Spec == log = <<>> /\ [][\E s \in Seq(S) : log' = log \o <<s>>]_log
====
```

## Problem

When you run the above TLA+ specification through TLC, you will encounter the following error:

```
TLC encountered the non-enumerable quantifier bound
Seq({"a", "b"})
line 8, col 35 to line 8, col 40 of module Simple
In TLA+, Seq(S) represents the set of all finite sequences whose elements come from the set S. Even when S
is a finite set, the number of possible sequences in Seq(S) is unbounded because sequences can have any
finite length (e.g., length 0, 1, 2, and so on). As a result, TLC cannot evaluate expressions that
universally (\A) or existentially (\E) quantify over Seq({"a", "b"}), because this would require checking an
infinite number of cases. Note that for a finite set of sequences s, TLC handles s \subseteq Seq(S).
```

The issue arises from using `Seq(S)` in your specification. In TLA+, `Seq(S)` denotes the set of all finite 
sequences formed from elements of `S`. Even if `S` is finite, `Seq(S)` is an **infinite** set because sequences
can have any length (0, 1, 2, and so on). However, TLC requires all sets to be finite and enumerable . As a
result, expressions like `\E s \in Seq(S): ...` or `\A s \in Seq(S): ...` cause this error because TLC cannot
handle infinite sets.

## Workaround

`BoundedSeq` is an operator from the [SequencesExt.tla](https://github.com/tlaplus/CommunityModules/blob/master/modules/SequencesExt.tla)
module in the [CommunityModules library](https://modules.tlapl.us). `BoundedSeq` is a **bounded version of
`Seq(S)`**, where you specify the **maximum allowed sequence length**. This makes the resulting set finite
and enumerable for TLC.

For example, `BoundedSeq({a, b}, 2)` is the (finite) set of sequences 
`{<<>>, <<"a">>, <<"b">>, <<"a", "a">>, <<"a", "b">>, <<"b", "a">>, <<"b", "b">>}`.

---

## How to Use `BoundedSeq` in Your Spec

To make your specification compatible with TLC, you can replace all instances of `Seq` with `BoundedSeq` and
define a maximum sequence length. However, this alters the original specification’s semantics. For example,
in the original version above, the log variable can be extended by a sequence of any length in each action,
whereas the modified version would only allow sequences up to length 2.

### 1. Create or Modify a Wrapper Spec (e.g., `MCSpec.tla`)

The canonical way to encapsulate `BoundedSeq`, like any other modifications required to use TLC is to create
a new module (by convention named to prefix the original module name with `MC`, such as `MCSimple.tla`) that
extends your original spec (e.g., `Simple.tla`). This way, you can keep the original spec intact while
providing a bounded version for model checking.

The canonical approach for adapting a specification to TLC is to create a separate module. By convention,
this module is named by adding the prefix `MC` to the original module name (e.g., `MCSimple.tla` for
`Simple.tla`). This new module should extend the original specification, allowing you to define a bounded
version suitable for model checking while keeping the original spec unchanged.


```tla
---- MODULE MCSimple ----
EXTENDS Simple, SequencesExt

MaxBoundedSeq == 2

MCSeq(S) ==
    BoundedSeq(S, MaxBoundedSeq)
====
```

---

### 2. Configure Your Model in `MCSimple.cfg`

In the configuration file `MCSimple.cfg`, you need to tell TLC to use your new bounded version of `Seq`:

```
SPECIFICATION Spec

CONSTANT
    \* TLC will generate all sequences up to and include length 2 when evaluating Seq(S).
    Seq <- MCSeq
```

When you run TLC on `MCSimple.tla`, this tells TLC to substitute `MCSeq` for every occurrence of `Seq` in
the model. Be sure to choose a `MaxBoundedSeq` value that includes the behaviors you're interested in,
while keeping the state space within a manageable size.
