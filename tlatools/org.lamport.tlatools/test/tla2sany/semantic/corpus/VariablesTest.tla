-------------------------- MODULE VariablesTest -----------------------------
EXTENDS Semantics
VARIABLES
  (* ID: x *) x,
  (* ID: y *) y,
  (* ID: z *) z

THEOREM RefersTo(x, "x")
THEOREM RefersTo(y, "y")
THEOREM RefersTo(z, "z")
THEOREM IsLevel(x, VariableLevel)
THEOREM IsLevel(y, VariableLevel)
THEOREM IsLevel(z, VariableLevel)

=============================================================================
