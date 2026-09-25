---
title: TLA+ Specification Review Guidelines
description: Best practices for reviewing and validating TLA+ specifications. Covers model checking, simulation, spec structure, constants, variables, invariants, properties, fairness constraints, and documentation standards.
---

# TLA+ Specification Review Guidelines

When reviewing a TLA+ specification, systematically work through each guideline in this document one by one. For each guideline, evaluate whether the specification adheres to it, and if not, provide specific feedback on how to improve. Do not skip guidelines or combine them—methodical, item-by-item review ensures thorough coverage and helps catch issues that might otherwise be overlooked.

This document uses a **producer-consumer** (bounded buffer) specification as a running example to illustrate the guidelines. In this system, producers add items to a shared buffer while consumers remove items from it.

## TLA+ Formulas

### Functions, Records, and Sequences

* Constructing a full record inside an `EXCEPT` expression where unchanged fields are explicitly assigned their current values is a code smell. For example:
  ```tla
  producers' = [producers EXCEPT ![p] = 
                 [count |-> producers[p].count + 1,
                  waiting |-> producers[p].waiting,
                  id |-> producers[p].id]]
  ```
  Here, `waiting` and `id` are redundantly restated. Use nested `EXCEPT` syntax instead to specify only what changes:
  ```tla
  producers' = [producers EXCEPT ![p].count = @ + 1]
  ```
  See `tla-functions-records-sequences.md` for details on `EXCEPT` and nested updates.

## Spec Structure

* Use SANY to perform syntax and level-checking of a TLA+ module before reviewing. This catches syntax errors early and ensures the spec is well-formed. If you are an AI assistant, use the `tlaplus_mcp_sany_parse` tool to parse the spec.

### Module

* The TLA+ CommunityModules are a collection of modules that provide useful operators and definitions for TLA+. Use of the CommunityModules is encouraged because most are well-tested and well-documented. Some operators even have TLC Java overrides that make them more efficient. The CommunityModules are available at https://github.com/tlaplus/CommunityModules, but they are already readily available in the VSCode/Cursor extension without manual installation.

* Use the `tlaplus_mcp_sany_modules` tool to list all available TLA+ modules, including the CommunityModules. Use the `tlaplus_mcp_sany_symbol` tool to extract and inspect the symbols (constants, operators, definitions) defined in any module.

* `EXTENDS TLC` is rarely needed in ordinary TLA+ specs. The operators defined in the TLC module are for special use cases.
  - The only notable exception is the `TLC!@@` operator, which merges two functions.
  - The use of `RandomElement` is almost always wrong. Use non-determinism (`\E` or disjunction) instead. See `tla-RandomElement.md` for details.
  - Use of `TLC!Assert` is discouraged in plain TLA+ specs. `Assert` is primarily used in PlusCal specs. An invariant is a better alternative, and TLC will report a counterexample if the invariant is violated.

### Constants and Assumptions

* If the spec declares constants, state assumptions that constrain their values. Ensure all constants have appropriate assumptions - for example, if declaring constants `NumProducers` and `NumConsumers`, use `ASSUME NumProducers \in Nat \ {0}` and `ASSUME NumConsumers \in Nat \ {0}` rather than only constraining one. Assumptions should be comprehensive and prevent nonsensical constant combinations (e.g., ensuring `BufferSize > 0`). TLC will refuse to check the spec if assumptions are violated, and assumptions aid readers in understanding the spec and are crucial for proving properties with TLAPS. Note: assumptions can be combined into a single ASSUME statement using conjunction, but TLC will not report which conjunct is violated, only that the assumption is violated. Assumptions may be named, e.g., `ASSUME ProducerAssumption == NumProducers \in Nat \ {0}`. It is good practice to name assumptions so they can be referred to in proofs.

* When order is irrelevant (i.e., the parameter is a symmetry set), use model values rather than integer intervals for constants. For example, instead of defining `Producers == 1..NumProducers`, make `Producers` a CONSTANT whose value is defined in the TLC configuration like `{P, Q}`. This improves readability and makes traces easier to understand.

* When using specific constant values in configuration files (like `BufferSize = 3`), document or justify why those particular values were chosen. Magic numbers should be explained with comments, especially if the choice affects the tractability or correctness of model checking.

* Beginners tend to conflate TLA+ and TLC. However, TLC is but one verification tool for TLA+. Thus, a spec should not depend on TLC-specific features and should remain general. To specialize specs for model checking, create an MC.tla file that extends the original spec and *redefines* constants or the `Init` predicate to constrain the state space. For example, redefine `Nat` as `{0,1,2,3}` or redefine `Init` (as `MCInit` assigned via substitution in the TLC config) to start from specific initial states that make model checking more tractable.

* Prefer using TLC's `CONSTRAINT` (state constraint) configuration to bound the model instead of adding artificial enablement conditions in actions. For example, instead of adding `produced <= MaxProduced` as an enablement condition in a `Produce` action, keep the action general and add `CONSTRAINT StateConstraint` where `StateConstraint == produced <= MaxProduced` in the TLC configuration. This separates model-checking concerns from the specification itself. See `tlc-config-files.md` for full TLC configuration file documentation.

### Variables

* Auxiliary variables are used to store (some of) the history of the system's state to be used in invariants or properties. A history variable may have any name, but it doesn't appear in the enablement conditions of actions of the next-state relation. In other words, a history variable doesn't affect the behavior of the system. It is good practice to choose a name for a history variable that indicates its purpose. For example, if the variable tracks how many items each producer has produced, name it `producedCount` rather than something generic like `aux`. This allows the reader to quickly identify the purpose of the variable. Introduce auxiliary variables when strictly necessary to express an invariant or property—each additional variable increases the state space, potentially making model checking intractable.

### Init

* The `Init` predicate in the main spec should be kept general and abstract, representing all valid initial states of the system. For model checking with TLC, use an MC.tla file to specialize the initial state (see Constants and Assumptions section).

### Next

* (Explicit) Actions that leave all variables unchanged are not needed; TLA+ specs are always invariant under stuttering because the next-state relation is written as [Next]_vars, which is equivalent to Next \/ UNCHANGED vars. See `tla-stuttering.md` for details.

* When using action constraints (via TLC's `ACTION_CONSTRAINT` configuration), verify that the constraints make sense given the initial conditions. For example, if `Init` starts with an empty buffer, and only `Produce` is enabled when the buffer is empty, ensure action constraints don't inadvertently prevent the `Produce` action from being explored.

* Be aware of the semantic differences between using if-then-else (ITE) in action definitions versus using enablement conditions. Using ITE (e.g., `IF Len(buffer) < BufferSize THEN ... ELSE UNCHANGED vars`) causes `ENABLED Produce` to always hold (the action is always enabled), whereas an enablement condition (e.g., `Len(buffer) < BufferSize /\ ...`) means the action is only enabled when the buffer has space. This distinction can lead to subtle differences when reasoning about fairness constraints. Choose the appropriate form based on whether the action should be considered enabled in all states or only when specific conditions hold.

### Spec

* In order to check liveness properties, a spec has to assert suitable fairness constraints. In most cases, a fairness constraint asserts weak or strong fairness over the next-state relation, or over individual sub-actions of the next-state relation. Other fairness constraints may result in the spec being non-machine closed, which is a very advanced topic and should be avoided by beginners.

* Fairness constraints should only be added where logically necessary to capture the intended system behavior. Not every action needs fairness - for example, producers that aren't required to produce forever, or actions modeling failures like dropping an item. Consider carefully whether each fairness constraint is justified by the system's actual requirements. Prefer weak fairness (`WF_vars(Consume)`) over strong fairness (`SF_vars(Consume)`) when sufficient, as weak fairness is simpler to reason about and generally adequate unless an action needs to be taken even when only occasionally enabled. Test with TLC to verify whether weak fairness suffices before using strong fairness.

### Invariants

* Every specification should include a `TypeOK` invariant that checks type correctness of all variables; a conjunction of formulas `var \in S` for each variable and an appropriate set `S`. For example, write `producedCount \in [Producers -> Nat]` rather than `\A p \in Producers : producedCount[p] \in Nat`. This helps catch type errors early and serves as documentation of the expected types. Define `TypeOK` close to the variable declarations so that readers understand the expected types.

* Include invariants for "obvious" properties even if they seem trivial from the protocol. These invariants serve as documentation, help catch subtle bugs, and provide additional confidence in the specification. For example, in a producer-consumer system, explicitly check that `Len(buffer) <= BufferSize` (buffer never overflows) and `consumed <= produced` (consumers never consume more than was produced), even if these seem obvious from the design.

* State predicates `P` (formulas that don't use primed variables or temporal operators like `[]P`, `<>P`) should be checked as `INVARIANT` rather than as temporal properties in the TLC configuration. This provides better performance.

* Check all defined invariants separately in the TLC configuration, not combined with other invariants as conjunction of invariants. This enables TLC to report which invariant is violated. See `tla-no-conjunct-of-invariants.md` for details.

### Properties

* Important properties should be declared as THEOREMs in the specification (e.g., `THEOREM Spec => EventuallyConsumed`). This serves as documentation of the key properties the spec is intended to satisfy and makes it clear what should be verified. However, don't include theorems that are not proven or checked with TLAPS or -at a minimum- checked with TLC.

* Liveness properties should typically ensure repeated behavior rather than just single occurrences. For example, instead of checking that a consumer eventually consumes once (`<>(consumed > 0)`), check that consumers keep making progress (e.g., `[]<>(buffer = <<>>)` — the buffer is empty infinitely often). This ensures the system doesn't just satisfy the property once and then deadlock or stop making progress.

* If liveness properties hold even without fairness, the property or fairness constraints need revision.

### Readability and Documentation

* Use meaningful and descriptive names for all identifiers (variables, constants, operators, actions). Names should clearly convey the purpose and meaning of the entity they represent. For example, prefer `buffer`, `Produce`, and `Consume` over generic names like `data`, `Action1`, and `Action2`.

* Organize the specification logically with related definitions grouped together. Prioritize readability over space efficiency - specifications are meant to be understood by humans, not optimized for memory usage.

* Each specification should include sufficient inline comments to explain the problem being modeled, key design decisions, and non-obvious logic. Comments should provide context that helps readers understand the specification without many external references. Consider using section comments to separate major parts of the specification (e.g., "---- Variables ----", "---- Actions ----").

* Programmers have internalized the DRY (Don't Repeat Yourself) principle. However, specs are short and rarely span multiple files. Thus, it is fine to relax DRY. Specifically, specs tend to be easier to read if they are written in a more verbose style, and similar patterns are not extracted into common definitions.

## Spec validation and verification with TLC

### Configuration file

* Consider whether deadlock checking is appropriate for your spec. Some specs legitimately terminate (e.g., when producers stop producing and consumers finish consuming all items from the buffer), and reporting this as a deadlock would be a false positive. In such cases, disable deadlock checking in the TLC configuration with `CHECK_DEADLOCK FALSE`. Additionally, consider adding an invariant that characterizes states in which the system may terminate, for example
`(~ ENABLED Next) <=> buffer = <<>>`.

### Simulation and Exhaustive Model Checking

* It is good practice to validate the spec with TLC's simulation mode. Simulation usually catches many shallow bugs that model checking may only catch after a long time. This is because model checking explores the entire state space breadth-first, while simulation immediately explores long traces. Simulation will run forever unless it finds a bug or is terminated by the user. Running TLC on a spec shall not report any warnings or errors—any warnings or errors should be investigated and fixed. Use the `tlaplus_mcp_tlc_smoke` tool to run TLC in simulation mode for smoke testing. 

* In addition to simulation and exploration, perform exhaustive model checking to verify that all reachable states satisfy the specified invariants and properties. To keep checking tractable, rely on the small-scope hypothesis: most bugs manifest even in small configurations of the system. For example, most bugs in a producer-consumer system will be found with one or two producers, one or two consumers, and a buffer of size between 1 and 3. TLC's configuration file should be set to a small enough configuration to make model checking tractable. See `tla-different-configurations.md` for guidance on checking models across different constant combinations. Use the `tlaplus_mcp_tlc_check` tool to perform exhaustive model checking of a TLA+ specification.

### Always Be Suspicious of Success

"Always Be Suspicious of Success" when TLC reports that all invariants and properties hold. This success may be vacuous: a spec that does nothing—or explores only a tiny fraction of the intended behaviors—will trivially satisfy any property without providing meaningful assurance. Likewise, a spec that doesn't match the author's intent offers no value, even if it passes all checks. Passing model checking is only meaningful when two conditions are met: the spec faithfully captures the intended system behavior, and the invariants and properties are strong enough to detect real bugs.

#### Exploration

* Use the `tlaplus_mcp_tlc_explore` tool to generate random behaviors of a given length. Sanity check for plausibility as many traces as practical to validate that the spec captures the intended system behaviors—each trace should represent a plausible execution of the system. Look for unexpected state transitions and implausible combinations of variable values. This manual inspection complements automated checking: simulation and model checking verify that invariants and properties hold, but only human review can confirm that the modeled behaviors match the designer's intent.

#### Bug Injection

* To validate that the invariants and properties are strong enough, intentionally inject bugs into the state-machine spec (the `Spec` and its sub-formulas) while leaving the invariants and properties untouched. If a bug doesn't cause any invariant or property violation, it suggests that the spec's correctness conditions are incomplete or too weak. Common mutations to try include:
  - Removing an enablement condition from an action (e.g., allow `Produce` even when the buffer is full)
  - Changing an arithmetic operator (e.g., `+` to `-`, `<` to `<=`)
  - Weakening a condition (e.g., change `x > 0` to `x >= 0`)
  - Removing a disjunct from the next-state relation (e.g., remove `Produce` from the next-state relation)
  - Removing (some of) the spec's fairness constraints
  - ... and many more.
Each injected bug should be caught by at least one invariant or property. If not, consider strengthening the correctness conditions or adding new ones that would detect the bug.

#### Coverage Statistics

* TLC reports coverage statistics. Check the number of (distinct) states reported by TLC: if this number is unreasonably low, the specification is likely to be irrelevant.

* Extended coverage statistics help identify which parts of the spec were exercised during model checking (run `tlaplus_mcp_tlc_check` with the `-coverage 1` option). Like line or statement coverage in traditional testing, TLC's coverage reveals "dead code"—formulas that are never evaluated to TRUE. Examples include IF-THEN-ELSE expressions where one branch is never taken, disjuncts that are never satisfied, or implications whose antecedent is never true.

* Beyond line-level coverage, TLC provides metrics specific to state-machine verification:
  - **State coverage per action**: For each action, TLC reports how many distinct states the action was enabled in, and how many state transitions it generated. If an action never fires (zero transitions), its enablement condition may be too restrictive or conflicting with other parts of the spec.
  - **Variable value coverage**: TLC tracks the distinct values each variable takes across all reachable states. Low value coverage for a variable (e.g., a counter that only reaches 0 or 1 when it could go higher) may indicate that the model's constants are too restrictive, or that certain behaviors are unreachable. Conversely, unexpectedly high value coverage might signal state-space explosion.

* Coverage statistics that show unexercised formulas or actions warrant investigation—they often point to spec bugs, overly constrained models, or genuinely unreachable code that should be removed.

* See https://explain.tlapl.us/module-coverage-statistics.md for details.