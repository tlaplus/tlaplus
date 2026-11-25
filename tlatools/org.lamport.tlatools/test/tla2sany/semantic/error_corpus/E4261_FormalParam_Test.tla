The @ symbol has special syntactic meaning and cannot be used as an
ordinary declared identifier, so it cannot be declared as a formal parameter.
---- MODULE E4261_FormalParam_Test ----
Foo(@) == 42
====
