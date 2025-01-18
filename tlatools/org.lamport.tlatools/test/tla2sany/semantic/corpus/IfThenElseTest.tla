-------------------------- MODULE IfThenElseTest ----------------------------
EXTENDS Semantics
CONSTANT (* ID: c *) c
VARIABLE (* ID: v *) v

THEOREM IsLevel(IF RefersTo(c, "c") THEN TRUE ELSE FALSE, ConstantLevel)
THEOREM IsLevel(IF TRUE THEN RefersTo(c, "c") ELSE FALSE, ConstantLevel)
THEOREM IsLevel(IF TRUE THEN FALSE ELSE RefersTo(c, "c"), ConstantLevel)
THEOREM IsLevel(IF RefersTo(v, "v") THEN TRUE ELSE FALSE, VariableLevel)
THEOREM IsLevel(IF TRUE THEN RefersTo(v, "v") ELSE FALSE, VariableLevel)
THEOREM IsLevel(IF TRUE THEN FALSE ELSE RefersTo(v, "v"), VariableLevel)
THEOREM IsLevel(IF RefersTo(v, "v")' THEN TRUE ELSE FALSE, ActionLevel)
THEOREM IsLevel(IF TRUE THEN RefersTo(v, "v")' ELSE FALSE, ActionLevel)
THEOREM IsLevel(IF TRUE THEN FALSE ELSE RefersTo(v, "v")', ActionLevel)
THEOREM IsLevel(IF []RefersTo(v, "v") THEN TRUE ELSE FALSE, TemporalLevel)
THEOREM IsLevel(IF TRUE THEN []RefersTo(v, "v") ELSE FALSE, TemporalLevel)
THEOREM IsLevel(IF TRUE THEN FALSE ELSE []RefersTo(v, "v"), TemporalLevel)
THEOREM IsLevel(IF RefersTo(c, "c") THEN RefersTo(v, "v") ELSE RefersTo(v, "v")', ActionLevel)
THEOREM IsLevel(IF RefersTo(v, "v") THEN RefersTo(v, "v")' ELSE []RefersTo(v, "v"), TemporalLevel)

=============================================================================

