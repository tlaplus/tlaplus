---- MODULE MC02 ----
EXTENDS EWD840, TLC, Sequences

const_143073460396411000 == 
    2

spec_143073460397412000 ==
    Spec /\ ENABLED Next /\ ENABLED (SelectSeq([i \in 1..N+1 |-> i - 1], LAMBDA node: node = tpos ) = <<tpos>>)

StateConstraint ==
    \* For the tests to be interesting, this triggers the evaluation 
    \* of a Java module override in one of TLC's standard modules that
    \* accesses a variable (the state) and involves EvalControl.
    \* Since we don't care about constraining the state space, this is
    \* a tautology.
    SelectSeq([i \in 1..N+1 |-> i - 1], LAMBDA node: node = tpos ) = <<tpos>>

ActionConstraint ==
    LET foo == SelectSeq([i \in 1..N+1 |-> i - 1], LAMBDA node: node = tpos )
    IN \/ foo = <<tpos>>'
       \/ foo # <<tpos'>>

-----------------------------------------------------------------------------

Stop == TLCGet("distinct") < 38

Alias ==
    [
         active |-> active,
         color |-> color,
         tpos |-> tpos,
         tcolor |-> tpos,
         enbld |-> ENABLED <<InitiateProbe>>_vars
    ]
    
=============================================================================
