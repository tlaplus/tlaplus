If a module tries to import a nonexistent spec, it should be an error.
---- MODULE E4220_Test ----
EXTENDS DoesNotExist12345
====

