------------------------ MODULE TLCGetNamedUndefined ------------------------
EXTENDS TLC

diameter == TLCGet("diameter")
distinct == TLCGet("distinct")
queue == TLCGet("queue")
level == TLCGet("level")

CONSTANT A,B,C,D

ASSUME(TRUE)

=============================================================================
