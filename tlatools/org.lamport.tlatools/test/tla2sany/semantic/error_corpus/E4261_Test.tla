The @ symbol has special syntactic meaning. As an expression it denotes
the previous value inside EXCEPT, and that use is an error anywhere else.
---- MODULE E4261_Test ----
op == @
====

