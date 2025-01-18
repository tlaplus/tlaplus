-------------------------- MODULE FunctionsTest -----------------------------
EXTENDS Semantics
CONSTANT (* ID: c *) c
VARIABLE (* ID: v *) v

(* ID: S *)
S == TRUE
THEOREM RefersTo(S, "S")
THEOREM IsLevel(S, ConstantLevel)

(* ID: f *)
f[(* ID: f!x *) x \in RefersTo(S, "S")] == RefersTo(x, "f!x")
THEOREM RefersTo(f, "f")
THEOREM IsLevel(f, ConstantLevel)

(* ID: g *)
g[(* ID: g!x *) x, (* ID: g!y *) y \in RefersTo(S, "S")] ==
  {RefersTo(x, "g!x"), RefersTo(y, "g!y")}
THEOREM RefersTo(g, "g")
THEOREM IsLevel(g, ConstantLevel)

(* ID: h *)
h[
    (* ID: h!x *) x, (* ID: h!y *) y \in RefersTo(S, "S"),
    (* ID: h!z *) z \in RefersTo(S, "S")
  ] == {RefersTo(x, "h!x"), RefersTo(y, "h!y"), RefersTo(z, "h!z")}
THEOREM RefersTo(h, "h")
THEOREM IsLevel(h, ConstantLevel)

(* ID: RF *)
RF[(* ID: RF!x *) x \in RefersTo(S, "S")] == RefersTo(RF, "RF")

(* ID: VariableBodyFunction *)
VariableBodyFunction[x \in RefersTo(S, "S")] == v
THEOREM RefersTo(VariableBodyFunction, "VariableBodyFunction")
THEOREM IsLevel(VariableBodyFunction, VariableLevel)

(* ID: ActionBodyFunction *)
ActionBodyFunction[x \in RefersTo(S, "S")] == v'
THEOREM RefersTo(ActionBodyFunction, "ActionBodyFunction")
THEOREM IsLevel(ActionBodyFunction, ActionLevel)

(* ID: TemporalBodyFunction *)
TemporalBodyFunction[x \in RefersTo(S, "S")] == []v
THEOREM RefersTo(TemporalBodyFunction, "TemporalBodyFunction")
THEOREM IsLevel(TemporalBodyFunction, TemporalLevel)

(* ID: VariableParameterFunction *)
VariableParameterFunction[x \in RefersTo(v, "v")] == c
THEOREM RefersTo(VariableParameterFunction, "VariableParameterFunction")
THEOREM IsLevel(VariableParameterFunction, VariableLevel)

(* ID: ActionParameterFunction *)
ActionParameterFunction[x \in RefersTo(v, "v")'] == c
THEOREM RefersTo(ActionParameterFunction, "ActionParameterFunction")
THEOREM IsLevel(ActionParameterFunction, ActionLevel)

\* Tests for calling functions
THEOREM IsLevel(f[RefersTo(c, "c")], ConstantLevel)
THEOREM IsLevel(f[RefersTo(v, "v")], VariableLevel)
THEOREM IsLevel(f[RefersTo(v, "v")'], ActionLevel)

THEOREM BasicFnExpr == IsLevel([
  (* ID: BasicFnExpr!x *) x \in RefersTo(S, "S") |->
    IsLevel(RefersTo(x, "BasicFnExpr!x"), ConstantLevel)
  ],
  ConstantLevel
)

THEOREM MultiVarFnExpr == IsLevel([
  (* ID: MultiVarFnExpr!x *) x, (* ID: MultiVarFnExpr!y *) y \in RefersTo(v, "v") |-> <<
    IsLevel(RefersTo(x, "MultiVarFnExpr!x"), ConstantLevel),
    IsLevel(RefersTo(y, "MultiVarFnExpr!y"), ConstantLevel)
  >>],
  VariableLevel
)

THEOREM TupleFnExpr == IsLevel([
  <<(* ID: TupleFnExpr!x *) x, (* ID: TupleFnExpr!y *) y>> \in RefersTo(S, "S")' |-> <<
    IsLevel(RefersTo(x, "TupleFnExpr!x"), ConstantLevel),
    IsLevel(RefersTo(y, "TupleFnExpr!y"), ConstantLevel)
  >>],
  ActionLevel
)

THEOREM MultiQuantFnExpr == IsLevel([
  <<(* ID: MultiQuantFnExpr!x *) x, (* ID: MultiQuantFnExpr!y *) y>> \in RefersTo(S, "S"),
  (* ID: MultiQuantFnExpr!z *) z \in RefersTo(c, "c") |-> <<
    IsLevel(RefersTo(x, "MultiQuantFnExpr!x"), ConstantLevel)',
    IsLevel(RefersTo(y, "MultiQuantFnExpr!y"), ConstantLevel),
    IsLevel(RefersTo(z, "MultiQuantFnExpr!z"), ConstantLevel)
  >>],
  ActionLevel
)

THEOREM ConstantFunctionSet == IsLevel(
  [RefersTo(S, "S") -> RefersTo(c, "c")],
  ConstantLevel
)

THEOREM SourceVariableFunctionSet == IsLevel(
  [RefersTo(v, "v") -> RefersTo(c, "c")],
  VariableLevel
)

THEOREM TargetVariableFunctionSet == IsLevel(
  [RefersTo(c, "c") -> RefersTo(v, "v")],
  VariableLevel
)

THEOREM SourceActionFunctionSet == IsLevel(
  [RefersTo(c, "c")' -> RefersTo(v, "v")],
  ActionLevel
)

THEOREM TargetActionFunctionSet == IsLevel(
  [RefersTo(c, "c") -> RefersTo(v, "v")'],
  ActionLevel
)

=============================================================================
