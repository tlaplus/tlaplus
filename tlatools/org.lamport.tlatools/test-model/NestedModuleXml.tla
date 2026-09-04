---- MODULE NestedModuleXml ----
\* A nested module that the enclosing module instantiates.
---- MODULE Instantiated ----
VARIABLE y
Foo == y = 42
====

\* A nested module that nothing refers to, extending a module that would
\* otherwise be absent from the export, and nesting a module of its own.
---- MODULE Standalone ----
EXTENDS Naturals

---- MODULE Innermost ----
Deep == TRUE
====

Bar == 1 + 1
====

VARIABLE x
Inst == INSTANCE Instantiated WITH y <- x
====
