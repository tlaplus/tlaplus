Module for checking semantic properties at parse time. Implementers of the
semantic parse corpus should search parse trees for usage of assertions
defined in this module, then implement appropriate logic to check them.

The RefersTo operator asserts that the given symbol refers to a definition
tagged with the given string ID in a comment. This operator is defined to
equal the given symbol so it can be dropped inside expressions without
altering their meaning; for example, it can be used inside IsLevel.

The IsLevel operator asserts that the given expression has the given level.
Similar to RefersTo, the operator is defined to equal the first parameter.
The expected action level must be given as a reference to the ConstantLevel,
VariableLevel, ActionLevel, or TemporalLevel operators.

Use ConstantLevel for expressions like TRUE, 5 or referring to CONSTANT c.
Use VariableLevel for expressions which refer to a VARIABLE x.
Use ActionLevel for expressions like x' or [P]_x or <<P>>_x.
Use TemporalLevel for expressions like []P or <>P or P ~> Q.

----------------------------- MODULE Semantics ------------------------------

(* ID: empty *)
LOCAL empty == "empty definition for writing assertions about assertion ops"

(* ID: Semantics!RefersTo *)
RefersTo(symbol, id) == symbol
ASSUME RefersTo(RefersTo(empty, "empty"), "Semantics!RefersTo")

(* ID: Semantics!ConstantLevel *)
ConstantLevel == "ConstantLevel"
ASSUME RefersTo(ConstantLevel, "Semantics!ConstantLevel")

(* ID: Semantics!VariableLevel *)
VariableLevel == "VariableLevel"
ASSUME RefersTo(VariableLevel, "Semantics!VariableLevel")

(* ID: Semantics!ActionLevel *)
ActionLevel == "ActionLevel"
ASSUME RefersTo(ActionLevel, "Semantics!ActionLevel")

(* ID: Semantics!TemporalLevel *)
TemporalLevel == "TemporalLevel"
ASSUME RefersTo(TemporalLevel, "Semantics!TemporalLevel")

(* ID: Semantics!IsLevel *)
IsLevel(expression, level) == expression
ASSUME RefersTo(IsLevel(empty, ConstantLevel), "Semantics!IsLevel")
ASSUME IsLevel(RefersTo(empty, "empty"), ConstantLevel)
ASSUME IsLevel(ConstantLevel, ConstantLevel)
ASSUME IsLevel(VariableLevel, ConstantLevel)
ASSUME IsLevel(ActionLevel, ConstantLevel)
ASSUME IsLevel(TemporalLevel, ConstantLevel)

=============================================================================
