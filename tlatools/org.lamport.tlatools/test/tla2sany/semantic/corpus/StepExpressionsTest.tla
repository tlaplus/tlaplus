------------------------ MODULE StepExpressionsTest -------------------------
EXTENDS Semantics

CONSTANT (* ID: c *) c
VARIABLES (* ID: v *) v

THEOREM IsLevel([RefersTo(c, "c")]_<<RefersTo(v, "v")>>, ActionLevel)
THEOREM IsLevel([RefersTo(v, "v")']_<<RefersTo(v, "v")>>, ActionLevel)
THEOREM IsLevel(<<RefersTo(c, "c")>>_<<RefersTo(v, "v")>>, ActionLevel)
THEOREM IsLevel(<<RefersTo(v, "v")'>>_<<RefersTo(v, "v")>>, ActionLevel)
THEOREM IsLevel([][RefersTo(c, "c")]_<<RefersTo(v, "v")>>, TemporalLevel)
THEOREM IsLevel([][RefersTo(v, "v")']_<<RefersTo(v, "v")>>, TemporalLevel)
THEOREM IsLevel(<><<RefersTo(c, "c")>>_<<RefersTo(v, "v")>>, TemporalLevel)
THEOREM IsLevel(<><<RefersTo(v, "v")'>>_<<RefersTo(v, "v")>>, TemporalLevel)

=============================================================================

