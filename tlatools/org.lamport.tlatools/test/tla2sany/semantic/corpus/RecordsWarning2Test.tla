--------------------------- MODULE RecordsWarning2Test ------------------------------
EXTENDS Semantics

CONSTANT (* ID: c *) c
VARIABLE (* ID: v *) v

Next ==
  [ c |-> v' ]

Init ==
  [ c |-> 42 ]

=============================================================================
