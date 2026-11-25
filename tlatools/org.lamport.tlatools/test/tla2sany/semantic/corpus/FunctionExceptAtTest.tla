------------------------- MODULE FunctionExceptAtTest ------------------------
EXTENDS Semantics

\* @ means the previous value of the function. This is valid when f is defined.
(* ID: f *)
f[x \in {1}] == 0

(* ID: AtExcept *)
AtExcept == [f EXCEPT ![1] = @]
THEOREM RefersTo(AtExcept, "AtExcept")
THEOREM IsLevel(AtExcept, ConstantLevel)

\* @ takes its level from the function. A variable in that function makes @
\* variable level.
VARIABLE (* ID: v *) v
(* ID: g *)
g[x \in {1}] == v

(* ID: VariableExceptAt *)
VariableExceptAt == [g EXCEPT ![1] = IsLevel(@, VariableLevel)]
THEOREM RefersTo(VariableExceptAt, "VariableExceptAt")
THEOREM IsLevel(VariableExceptAt, VariableLevel)

(* ID: PrimedConstantAt *)
PrimedConstantAt == [f EXCEPT ![1] = IsLevel(@', ActionLevel)]
THEOREM RefersTo(PrimedConstantAt, "PrimedConstantAt")
THEOREM IsLevel(PrimedConstantAt, ActionLevel)

(* ID: PrimedVariableAt *)
PrimedVariableAt == [g EXCEPT ![1] = IsLevel(@', ActionLevel)]
THEOREM RefersTo(PrimedVariableAt, "PrimedVariableAt")
THEOREM IsLevel(PrimedVariableAt, ActionLevel)

\* A prime in the function makes @ itself action level.
(* ID: a *)
a[x \in {1}] == v'

(* ID: ActionExceptAt *)
ActionExceptAt == [a EXCEPT ![1] = IsLevel(@, ActionLevel)]
THEOREM RefersTo(ActionExceptAt, "ActionExceptAt")
THEOREM IsLevel(ActionExceptAt, ActionLevel)

=============================================================================
