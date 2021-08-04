---- CONFIG Error02 ----
CONSTANT
N = 2
SPECIFICATION SillySpec
CONSTRAINT StateConstraint
ACTION_CONSTRAINT ActionConstraint
PROPERTIES Liveness
INVARIANT Inv
========================
---- MODULE Error02 ----
EXTENDS EWD840, TLC, Sequences

SillySpec ==
    Spec /\ 42 = "abc" \* Silly expression as the level of the behavior spec.

StateConstraint ==
    \* For the tests to be interesting, this triggers the evaluation 
    \* of a Java module override in one of TLC's standard modules that
    \* accesses a variable (the state) and involves EvalControl.
    \* Since we don't care about constraining the state space, this is
    \* a tautology.
    SelectSeq([i \in 1..N+1 |-> i - 1], LAMBDA node: node = "abc" ) = <<tpos>>

ActionConstraint ==
    LET foo(vv) == SelectSeq([i \in 1..N+1 |-> i - 1], LAMBDA node: node = vv )
    IN \/ foo("abc") = <<tpos>>'
       \/ foo("abc") # <<tpos'>>
    
=============================================================================
