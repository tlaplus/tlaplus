---- MODULE MC03Sim ----
EXTENDS EWD840, TLC, Sequences

Level ==
    TLCGet("level") < 15

ActionConstraint ==
    vars' # vars
=============================================================================
