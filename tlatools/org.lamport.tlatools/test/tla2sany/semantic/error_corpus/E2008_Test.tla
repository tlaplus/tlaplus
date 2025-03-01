If two distinct modules with the same name are imported into the same module,
this is an error.
---- MODULE E2008_Test ----
EXTENDS Naturals
---- MODULE Naturals ----
====
INSTANCE Naturals
====

