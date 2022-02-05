---- MODULE EWD840MC1 ----
EXTENDS EWD840, TLC

const_123 == 4

PostCondition ==
	TLCSet(42, TLCGet("generated"))
===================