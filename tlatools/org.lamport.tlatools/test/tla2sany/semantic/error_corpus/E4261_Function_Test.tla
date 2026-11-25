The @ symbol has special syntactic meaning and cannot be used as an
ordinary declared identifier, so it cannot be defined as a function.
---- MODULE E4261_Function_Test ----
@[x \in {0}] == 0
====
