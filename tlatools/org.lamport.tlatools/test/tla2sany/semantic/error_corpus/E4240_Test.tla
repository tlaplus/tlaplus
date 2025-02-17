When a module is imported with INSTANCE, all its constants and variables must
be assigned either implicitly or explicitly.
---- MODULE E4240_Test ----
---- MODULE Inner ----
CONSTANT c
====
INSTANCE Inner
====

