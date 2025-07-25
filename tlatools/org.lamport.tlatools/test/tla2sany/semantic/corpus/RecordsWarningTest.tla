--------------------------- MODULE RecordsWarningTest ------------------------------
EXTENDS Semantics

CONSTANT (* ID: c *) c
VARIABLE (* ID: v *) v

Init ==
  [ c |-> 42, frob |-> "hello" ]

Next ==
  [ frob |-> "world", c |-> v' ]

=============================================================================
