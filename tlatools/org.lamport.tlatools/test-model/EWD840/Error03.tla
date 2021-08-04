---- CONFIG Error03 ----
CONSTANT
N = 2
SPECIFICATION Spec
ACTION_CONSTRAINT ActionConstraint
PROPERTIES Liveness
INVARIANT Inv
========================
---- MODULE Error03 ----
EXTENDS EWD840, TLC, Sequences

ActionConstraint ==
    LET foo(vv) == SelectSeq([i \in 1..N+1 |-> i - 1], LAMBDA node: node = vv )
    IN \/ foo("abc") = <<tpos>>'
       \/ foo("abc") # <<tpos'>>
    
=============================================================================
