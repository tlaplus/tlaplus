# When to use INVARIANT/INVARIANTS and when to use PROPERTY/PROPERTIES with TLC?

The `INVARIANT` (or `INVARIANTS`) keyword in a TLC configuration file is used to specify a state-level (level 1) formula—a condition that must hold in all reachable states of the system. This is typically how safety properties are expressed—asserting that "something bad never happens." For instance, an invariant might state that a certain variable is always non-negative.
A state-level (level 1) formula is a predicate about the values of state variables in a single state. It contains state variables but no primed variables and no temporal operators.

However, the same condition can also be written as a temporal-level (level 3) formula using TLA+ syntax. In this case, assuming an invariant `I`, it would be written as `[]I` (read as "always I") in the TLA+ specification. Then, in the config file, instead of using `INVARIANT I`, you would use `PROPERTY []I`.
A temporal-level (level 3) formula contains temporal operators such as `[]` (always), `<>` (eventually), or the leads-to operator `~>`, and expresses properties about sequences of states.

Important note: If you switch from `INVARIANT I` to `PROPERTY I` without updating the definition of `I` to include the temporal `[]` operator, the meaning changes drastically. Without the `[]`, TLC will only check that `I` holds in the initial states—not in all reachable states—potentially missing violations of the intended property.