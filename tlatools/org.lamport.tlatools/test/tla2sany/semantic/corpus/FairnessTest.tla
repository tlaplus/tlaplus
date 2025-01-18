--------------------------- MODULE FairnessTest -----------------------------
EXTENDS Semantics

VARIABLES (* ID: x *) x, (* ID: y *) y, (* ID: z*) z

(* ID: vars *)
vars == <<x, y, z>>

THEOREM IsLevel(WF_RefersTo(vars, "vars")(1), TemporalLevel)
THEOREM IsLevel(WF_<<RefersTo(x, "x"), RefersTo(y, "y"), RefersTo(z, "z")>>(1), TemporalLevel)
THEOREM IsLevel(SF_RefersTo(vars, "vars")(1), TemporalLevel)
THEOREM IsLevel(SF_<<RefersTo(x, "x"), RefersTo(y, "y"), RefersTo(z, "z")>>(1), TemporalLevel)

THEOREM IsLevel(WF_RefersTo(vars, "vars")(RefersTo(x, "x")), TemporalLevel)
THEOREM IsLevel(SF_RefersTo(vars, "vars")(RefersTo(y, "y")), TemporalLevel)

THEOREM IsLevel(WF_RefersTo(vars, "vars")(RefersTo(z, "z")'), TemporalLevel)
THEOREM IsLevel(SF_RefersTo(vars, "vars")(RefersTo(x, "x")'), TemporalLevel)

=============================================================================

