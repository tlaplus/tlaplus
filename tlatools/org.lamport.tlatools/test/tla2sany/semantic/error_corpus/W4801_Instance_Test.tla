If two modules are imported using INSTANCE and they both define the same
symbol, generate a warning since the symbol in the module imported second is
ignored in favor of the definition from the module imported first.
---- MODULE W4801_Instance_Test ----
---- MODULE Inner ----
Nat == TRUE
====
INSTANCE Inner
INSTANCE Naturals
====

